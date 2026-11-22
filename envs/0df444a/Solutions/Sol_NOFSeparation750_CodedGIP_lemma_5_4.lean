-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-22T21:08:04.296588+00:00
-- url     : https://prove2.me/submissions/1169ae0f-c567-4c09-945b-01308e7cb95f

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders

open NOFSeparation750.CodedGIP Finset

namespace L54Aux

theorem exists_infoSet {F : Type} [Field F] {r : ℕ} (V : Submodule F (Fin r → F)) (m : ℕ)
    (hm : Module.finrank F V = m) :
    ∃ S : Fin m → Fin r, Function.Injective (fun a : V => fun j => a.val (S j)) := by
  classical
  let s : Set (Module.Dual F V) :=
    Set.range (fun t : Fin r => (LinearMap.proj t : (Fin r → F) →ₗ[F] F).comp V.subtype)
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent F s
  have hsep : ∀ a : V, (∀ f ∈ b, f a = 0) → a = 0 := by
    intro a ha
    have hle : Submodule.span F b ≤ LinearMap.ker (Module.Dual.eval F V a) :=
      Submodule.span_le.mpr fun f hf => by simpa using ha f hf
    apply Subtype.ext; funext t
    have hmem : (LinearMap.proj t : (Fin r → F) →ₗ[F] F).comp V.subtype ∈ Submodule.span F b := by
      rw [hspan]; exact Submodule.subset_span ⟨t, rfl⟩
    have := hle hmem
    simpa using this
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  let _ : Fintype b := hfin.fintype
  have hcard_le : Fintype.card b ≤ m := by
    have := hli.fintype_card_le_finrank
    rwa [Subspace.dual_finrank_eq, hm] at this
  let ev : V →ₗ[F] (b → F) :=
    { toFun := fun a f => (f : Module.Dual F V) a
      map_add' := fun a a' => by funext f; simp
      map_smul' := fun c a => by funext f; simp }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hsep a fun f hf => congrFun ha ⟨f, hf⟩
  have hcard_ge : m ≤ Fintype.card b := by
    have := LinearMap.finrank_le_finrank_of_injective hev
    rwa [hm, Module.finrank_fintype_fun_eq_card] at this
  have hcard : Fintype.card b = m := le_antisymm hcard_le hcard_ge
  let eb : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hT : ∀ f : b, ∃ t : Fin r,
      (LinearMap.proj t : (Fin r → F) →ₗ[F] F).comp V.subtype = (f : Module.Dual F V) :=
    fun f => hbs f.2
  choose T hT using hT
  refine ⟨fun j => T (eb j), ?_⟩
  intro a a' haa
  have h0 : a - a' = 0 := by
    apply hsep
    intro f hf
    obtain ⟨j, hj⟩ := eb.surjective ⟨f, hf⟩
    have e := congrFun haa j
    have := hT (eb j)
    rw [hj] at this
    have this' : (LinearMap.proj (T ⟨f, hf⟩) : (Fin r → F) →ₗ[F] F).comp V.subtype = f := this
    rw [← this']
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearMap.coe_proj, Function.eval, Submodule.coe_sub, Pi.sub_apply]
    simp only at e
    rw [hj] at e
    rw [e, sub_self]
  exact sub_eq_zero.mp h0

end L54Aux

theorem solution (k ℓ r : ℕ) (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (F : Type) [Field F] [Fintype F] (D : CodePair F r)
    (A : Set (Fin k → Forehead D ℓ)) (hA : IsCylinderIntersection A)
    (hAccept : A ⊆ {x | codedGIP D ℓ k x = true})
    (c : Fin k → D.large.code) :
    ∃ B : Set (Fin k → Fin (ℓ * D.small.dimension) → F), ∃ τ : F,
      IsCylinderIntersection B ∧
      uniformMass B = conditionalMass A {x | ∀ i, (x i).2 = c i} ∧
      B ⊆ {y | gip y = τ} := by
  classical
  set m := D.small.dimension with hm
  have hfr : Module.finrank F D.small.code = m := by
    rw [Module.finrank_eq_card_basis D.small.basis, Fintype.card_fin]
  obtain ⟨S, hS⟩ := L54Aux.exists_infoSet D.small.code m hfr
  let res : D.small.code →ₗ[F] (Fin m → F) :=
    { toFun := fun a j => a.val (S j)
      map_add' := fun a a' => by funext j; simp
      map_smul' := fun c a => by funext j; simp }
  have hres_inj : Function.Injective res := hS
  have hres_surj : Function.Surjective res := by
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hres_inj
    · rw [hfr, Module.finrank_fin_fun]
  let ρ : D.small.code ≃ₗ[F] (Fin m → F) := LinearEquiv.ofBijective res ⟨hres_inj, hres_surj⟩
  have hρ : ∀ a j, ρ a j = a.val (S j) := fun a j => rfl
  let e : Fin ℓ × Fin m ≃ Fin (ℓ * m) := finProdFinEquiv
  let Φ : (Fin k → Fin (ℓ * m) → F) → (Fin k → Forehead D ℓ) := fun y i =>
    (fun h => ρ.symm (fun j => y i (e (h, j))), c i)
  set E : Set (Fin k → Forehead D ℓ) := {x | ∀ i, (x i).2 = c i} with hE
  have hΦE : ∀ y, Φ y ∈ E := fun y i => rfl
  let Ψ : (Fin k → Fin (ℓ * m) → F) ≃ {x // x ∈ E} :=
    { toFun := fun y => ⟨Φ y, hΦE y⟩
      invFun := fun x i p => ρ ((x.1 i).1 (e.symm p).1) (e.symm p).2
      left_inv := fun y => by
        funext i p
        simp only [Φ, LinearEquiv.apply_symm_apply]
        rw [Prod.mk.eta, Equiv.apply_symm_apply]
      right_inv := fun x => by
        apply Subtype.ext
        funext i
        obtain ⟨x, hx⟩ := x
        simp only [Φ]
        refine Prod.ext ?_ (hx i).symm
        funext h
        simp only [Equiv.symm_apply_apply]
        exact ρ.symm_apply_apply _ }
  refine ⟨Φ ⁻¹' A, ∑ j : Fin m, ∑ i : Fin k, (c i).val (S j), ?_, ?_, ?_⟩
  · obtain ⟨C, hC, rfl⟩ := hA
    refine ⟨fun i => Φ ⁻¹' C i, fun i => ?_, by ext y; simp⟩
    intro y y' hyy
    simp only [Set.mem_preimage]
    apply hC i
    intro j hj
    simp only [Φ, hyy j hj]
  · unfold uniformMass conditionalMass
    have h1 : Nat.card {x // x ∈ Φ ⁻¹' A} = Nat.card {x // x ∈ A ∩ E} := by
      refine Nat.card_congr
        { toFun := fun y => ⟨Φ y.1, y.2, hΦE y.1⟩
          invFun := fun x => ⟨Ψ.symm ⟨x.1, x.2.2⟩, ?_⟩
          left_inv := fun y => by
            apply Subtype.ext
            exact Ψ.left_inv y.1
          right_inv := fun x => Subtype.ext (by
            show Φ (Ψ.symm ⟨x.1, x.2.2⟩) = x.1
            exact congrArg Subtype.val (Ψ.apply_symm_apply ⟨x.1, x.2.2⟩)) }
      have := congrArg Subtype.val (Ψ.right_inv ⟨x.1, x.2.2⟩)
      simp only [Set.mem_preimage]
      change Φ (Ψ.symm ⟨x.1, x.2.2⟩) ∈ A
      have h' : Φ (Ψ.symm ⟨x.1, x.2.2⟩) = x.1 := this
      rw [h']; exact x.2.1
    have h2 : Nat.card (Fin k → Fin (ℓ * m) → F) = Nat.card {x // x ∈ E} := Nat.card_congr Ψ
    rw [h1, h2]
  · intro y hy
    have hacc := hAccept hy
    simp only [Set.mem_ofPred_eq, codedGIP, decide_eq_true_eq] at hacc
    simp only [Set.mem_ofPred_eq]
    have key : ∀ (h : Fin ℓ) (i : Fin k) (j : Fin m),
        ((Φ y i).1 h).val (S j) = y i (e (h, j)) := by
      intro h i j
      rw [← hρ]; simp [Φ]
    calc gip y = ∑ p : Fin ℓ × Fin m, ∏ i, y i (e p) := by
          unfold gip; exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
      _ = ∑ j : Fin m, ∑ h : Fin ℓ, ∏ i, ((Φ y i).1 h).val (S j) := by
          rw [Fintype.sum_prod_type, sum_comm]; simp only [key]
      _ = ∑ j : Fin m, (∑ h : Fin ℓ, (fun t => ∏ i, ((Φ y i).1 h).val t)) (S j) := by
          simp [Finset.sum_apply]
      _ = ∑ j : Fin m, ∑ i : Fin k, (c i).val (S j) := by
          refine sum_congr rfl fun j _ => ?_
          rw [hacc]; simp [Finset.sum_apply, Φ]
