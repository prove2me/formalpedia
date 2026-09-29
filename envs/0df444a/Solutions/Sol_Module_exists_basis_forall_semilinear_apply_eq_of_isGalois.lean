-- Prove2me | solution 1 for Module.exists_basis_forall_semilinear_apply_eq_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3e017ab6-c21e-5042-b91a-995cc9887142

import Mathlib
import Theorems.Thm_Submodule_span_fixedPoints_semilinear_eq_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IntermediateField

theorem solution
    (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v))
    (hopen : ∀ v : V, ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ : L ≃ₐ[K] L, σ ∈ E.fixingSubgroup → ρ σ v = v) :
    ∃ b : Module.Basis (Fin (Module.finrank L V)) L V, ∀ (i : Fin (Module.finrank L V)) (σ : L ≃ₐ[K] L),
      ρ σ (b i) = b i := by
  classical

  let e : Module.Basis (Fin (Module.finrank L V)) L V := Module.finBasis L V
  choose E hEfd hEfix using fun i : Fin (Module.finrank L V) => hopen (e i)
  haveI : ∀ i, FiniteDimensional K (E i) := hEfd
  let E₀ : IntermediateField K L := ⨆ i, E i
  haveI : FiniteDimensional K E₀ := IntermediateField.finiteDimensional_iSup_of_finite
  let N : IntermediateField K L := normalClosure K E₀ L
  haveI : FiniteDimensional K N := normalClosure.is_finiteDimensional K E₀ L
  haveI : Normal K N := normalClosure.normal K E₀ L
  haveI : Algebra.IsSeparable K N := Algebra.isSeparable_tower_bot_of_isSeparable K N L
  haveI : IsGalois K N := IsGalois.mk
  have hEN : ∀ i, E i ≤ N := fun i => (le_iSup E i).trans (IntermediateField.le_normalClosure E₀)
  have hmemfix : ∀ (σ : L ≃ₐ[K] L), σ ∈ N.fixingSubgroup ↔ ∀ x ∈ N, σ x = x := fun σ => by
    rw [IntermediateField.mem_fixingSubgroup_iff]
  have hfixN : ∀ i (σ : L ≃ₐ[K] L), σ ∈ N.fixingSubgroup → ρ σ (e i) = e i := by
    intro i σ hσ
    apply hEfix i σ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    exact fun x hx => hσ x (hEN i hx)

  have hσN : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ N → σ x ∈ N := by
    intro σ x hx
    have := AlgEquiv.restrictNormal_commutes σ N ⟨x, hx⟩

    rw [show σ ((algebraMap (↥N) L) ⟨x, hx⟩) = σ x from rfl] at this
    rw [← this]
    exact (σ.restrictNormal N ⟨x, hx⟩).2
  have hconj : ∀ (σ h : L ≃ₐ[K] L), h ∈ N.fixingSubgroup → σ⁻¹ * h * σ ∈ N.fixingSubgroup := by
    intro σ h hh
    rw [hmemfix] at hh ⊢
    intro x hx
    show σ⁻¹ (h (σ x)) = x
    rw [hh _ (hσN σ x hx)]
    exact σ.symm_apply_apply x

  letI instNV : Module N V := Module.compHom V (algebraMap N L)
  have hsmulN : ∀ (a : N) (v : V), a • v = (algebraMap N L a) • v := fun _ _ => rfl

  let W : Submodule N V :=
    { carrier := {v | ∀ σ ∈ N.fixingSubgroup, ρ σ v = v}
      zero_mem' := fun σ _ => map_zero _
      add_mem' := fun {a b} ha hb σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]
      smul_mem' := fun a {v} hv σ hσ => by
        show ρ σ ((algebraMap N L a) • v) = (algebraMap N L a) • v
        rw [hρ_smul, hv σ hσ]
        congr 1
        exact (hmemfix σ).mp hσ _ a.2 }
  have hWmem : ∀ {v : V}, v ∈ W ↔ ∀ σ ∈ N.fixingSubgroup, ρ σ v = v := Iff.rfl
  have heW : ∀ i, e i ∈ W := fun i => hWmem.mpr (hfixN i)

  have hstab : ∀ (σ : L ≃ₐ[K] L) {v : V}, v ∈ W → ρ σ v ∈ W := by
    intro σ v hv h hh
    have h1 : h * σ = σ * (σ⁻¹ * h * σ) := by group
    rw [← hρ_mul, h1, hρ_mul, hv _ (hconj σ h hh)]

  have hagree : ∀ (σ τ : L ≃ₐ[K] L), σ.restrictNormal N = τ.restrictNormal N → ∀ {v : V}, v ∈ W → ρ σ v = ρ τ v := by
    intro σ τ hστ v hv
    have hmem : τ⁻¹ * σ ∈ N.fixingSubgroup := by
      rw [hmemfix]
      intro x hx
      show τ⁻¹ (σ x) = x
      have h1 := AlgEquiv.restrictNormal_commutes σ N ⟨x, hx⟩
      have h2 := AlgEquiv.restrictNormal_commutes τ N ⟨x, hx⟩
      rw [hστ] at h1
      have h1' : (algebraMap N L) (τ.restrictNormal N ⟨x, hx⟩) = σ x := h1
      have h2' : (algebraMap N L) (τ.restrictNormal N ⟨x, hx⟩) = τ x := h2
      have : σ x = τ x := by rw [← h1', h2']
      rw [this]
      exact τ.symm_apply_apply x
    have := hv _ hmem
    rw [hρ_mul] at this

    have h3 := congrArg (ρ τ) this
    rw [← hρ_mul, mul_inv_cancel, hρ_one] at h3
    exact h3

  let lift : (N ≃ₐ[K] N) → (L ≃ₐ[K] L) := fun τ => (AlgEquiv.restrictNormalHom_surjective L τ).choose
  have hlift : ∀ τ : N ≃ₐ[K] N, (lift τ).restrictNormal N = τ := fun τ =>
    (AlgEquiv.restrictNormalHom_surjective L τ).choose_spec
  let ρN : (N ≃ₐ[K] N) → W →+ W := fun τ =>
    { toFun := fun w => ⟨ρ (lift τ) w, hstab _ w.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hρN_apply : ∀ (τ : N ≃ₐ[K] N) (w : W), ((ρN τ w : W) : V) = ρ (lift τ) w := fun _ _ => rfl
  have hρN_smul : ∀ (τ : N ≃ₐ[K] N) (a : N) (w : W), ρN τ (a • w) = τ a • ρN τ w := by
    intro τ a w
    apply Subtype.ext
    show ρ (lift τ) ((algebraMap N L a) • (w : V)) = (algebraMap N L (τ a)) • ρ (lift τ) (w : V)
    rw [hρ_smul]
    congr 1
    have := AlgEquiv.restrictNormal_commutes (lift τ) N a
    rw [hlift] at this
    exact this.symm
  have hρN_one : ∀ w : W, ρN 1 w = w := by
    intro w
    apply Subtype.ext
    rw [hρN_apply]
    have h1 : (lift 1).restrictNormal N = (1 : L ≃ₐ[K] L).restrictNormal N := by
      rw [hlift]; exact (map_one (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) N)).symm
    rw [hagree _ _ h1 w.2, hρ_one]
  have hρN_mul : ∀ (σ τ : N ≃ₐ[K] N) (w : W), ρN (σ * τ) w = ρN σ (ρN τ w) := by
    intro σ τ w
    apply Subtype.ext
    rw [hρN_apply, hρN_apply, hρN_apply, ← hρ_mul]
    have h1 : (lift (σ * τ)).restrictNormal N = (lift σ * lift τ).restrictNormal N := by
      show AlgEquiv.restrictNormalHom N (lift (σ * τ)) = AlgEquiv.restrictNormalHom N (lift σ * lift τ)
      rw [map_mul]
      show (lift (σ * τ)).restrictNormal N = (lift σ).restrictNormal N * (lift τ).restrictNormal N
      rw [hlift, hlift, hlift]
    exact hagree _ _ h1 w.2

  letI instKW : Module K W := Module.compHom W (algebraMap K N)
  haveI : IsScalarTower K N W := ⟨fun k a w => by
    show ((k • a : N)) • w = (algebraMap K N k) • (a • w)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspanW := Submodule.span_fixedPoints_semilinear_eq_top K N W ρN hρN_smul hρN_one hρN_mul

  let S : Set V := {v | ∀ σ : L ≃ₐ[K] L, ρ σ v = v}
  have hfixedW_sub : ∀ w : W, (∀ τ : N ≃ₐ[K] N, ρN τ w = w) → (w : V) ∈ S := by
    intro w hw σ
    have h1 : (lift (σ.restrictNormal N)).restrictNormal N = σ.restrictNormal N := hlift _
    rw [← hagree _ _ h1 w.2, ← hρN_apply, hw]
  have hspanS : Submodule.span L S = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩

    have hi : (⟨e i, heW i⟩ : W) ∈ Submodule.span N {w : W | ∀ τ : N ≃ₐ[K] N, ρN τ w = w} := by
      rw [hspanW]; exact Submodule.mem_top
    have key : ∀ w : W, w ∈ Submodule.span N {w : W | ∀ τ : N ≃ₐ[K] N, ρN τ w = w} →
        (w : V) ∈ Submodule.span L S := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hfixedW_sub x hx)
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
        show (algebraMap N L a) • (x : V) ∈ Submodule.span L S
        exact Submodule.smul_mem _ _ hx
    exact key _ hi

  obtain ⟨t, htS, htsp, hli⟩ := exists_linearIndependent L S
  have htfin : t.Finite := hli.set_finite_of_isNoetherian
  haveI : Fintype t := htfin.fintype
  have htsp' : ⊤ ≤ Submodule.span L (Set.range ((↑) : t → V)) := by rw [Subtype.range_coe, htsp, hspanS]
  let b₀ : Module.Basis t L V := Module.Basis.mk hli htsp'
  have hcard : Fintype.card t = Module.finrank L V := (Module.finrank_eq_card_basis b₀).symm
  refine ⟨b₀.reindex (Fintype.equivFinOfCardEq hcard), fun i σ => ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  exact htS (Subtype.mem _) σ

end S_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois
end P2MW
export P2MW.S_Module_exists_basis_forall_semilinear_apply_eq_of_isGalois (solution)
