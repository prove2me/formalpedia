-- Prove2me | solution 1 for HopfAlgebra.hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a7578021-070e-55db-9f9e-06b0fb51be32

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage
import Theorems.Thm_Representation_exists_submodule_quotient_line_of_commutator_le_of_isPGroup
import Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField
import Theorems.Thm_HopfAlgebra_exists_fVectStructure_of_pointAction_of_bijective_evalPoints
import Theorems.Thm_HopfAlgebra_bijective_evalPoints_hopfKer_of_bijective_evalPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField
p2m_attr_erase "instance" "CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false

open scoped TensorProduct

universe u v

namespace S17C7

section PMod

variable (p : ℕ) (G : Type*) [CommGroup G]

abbrev powRange : Subgroup G := (powMonoidHom p : G →* G).range

abbrev PMod : Type _ := Additive (G ⧸ powRange p G)

variable {G}

theorem mem_powRange_iff (g : G) : g ∈ powRange p G ↔ ∃ t : G, t ^ p = g := MonoidHom.mem_range

def pcls (g : G) : PMod p G := Additive.ofMul (QuotientGroup.mk g : G ⧸ powRange p G)

theorem pcls_mul (g h : G) : pcls p (g * h) = pcls p g + pcls p h := by
  simp only [pcls, QuotientGroup.mk_mul, ofMul_mul]

theorem pcls_one : pcls p (1 : G) = 0 := by
  simp only [pcls, QuotientGroup.mk_one, ofMul_one]

theorem pcls_inv (g : G) : pcls p g⁻¹ = -pcls p g := by
  simp only [pcls, QuotientGroup.mk_inv, ofMul_inv]

theorem pcls_surjective : Function.Surjective (pcls p (G := G)) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  exact ⟨g, by simp only [pcls, hg]; rfl⟩

theorem pcls_pow_p (g : G) : pcls p (g ^ p) = 0 := by
  simp only [pcls, (QuotientGroup.eq_one_iff _).mpr ((mem_powRange_iff p _).mpr ⟨g, rfl⟩), ofMul_one]

theorem pcls_eq_iff (g h : G) : pcls p g = pcls p h ↔ ∃ t : G, h = g * t ^ p := by
  simp only [pcls, Additive.ofMul.injective.eq_iff, QuotientGroup.eq, mem_powRange_iff]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_inv_cancel_left]⟩
  · rintro ⟨t, rfl⟩; exact ⟨t, by rw [inv_mul_cancel_left]⟩

theorem p_nsmul_eq_zero (x : PMod p G) : p • x = 0 := by
  obtain ⟨g, rfl⟩ := pcls_surjective p x
  have : ∀ k : ℕ, k • pcls p g = pcls p (g ^ k) := by
    intro k
    induction k with
    | zero => rw [zero_nsmul, pow_zero, pcls_one]
    | succ k ih => rw [succ_nsmul, ih, pow_succ, pcls_mul]
  rw [this, pcls_pow_p]

scoped instance PMod.instModule : Module (ZMod p) (PMod p G) := AddCommGroup.zmodModule (p_nsmul_eq_zero p)

p2m_reactivate "P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField.S17C7.PMod"

def pmap (φ : G →* G) : PMod p G →+ PMod p G :=
  MonoidHom.toAdditive (QuotientGroup.map (powRange p G) (powRange p G) φ (by
    intro g hg
    obtain ⟨t, rfl⟩ := (mem_powRange_iff p _).mp hg
    exact (mem_powRange_iff p _).mpr ⟨φ t, by rw [← map_pow]⟩))

theorem pmap_pcls (φ : G →* G) (g : G) : pmap p φ (pcls p g) = pcls p (φ g) := rfl

def plin (φ : G →* G) : PMod p G →ₗ[ZMod p] PMod p G := (pmap p φ).toZModLinearMap p

theorem plin_apply (φ : G →* G) (x : PMod p G) : plin p φ x = pmap p φ x := rfl

def prep {Γ : Type*} [Group Γ] (a : Γ →* Monoid.End G) : Representation (ZMod p) Γ (PMod p G) where
  toFun γ := plin p (a γ)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨g, rfl⟩ := pcls_surjective p x
    rw [plin_apply, pmap_pcls, map_one]
    rfl
  map_mul' γ δ := by
    apply LinearMap.ext
    intro x
    obtain ⟨g, rfl⟩ := pcls_surjective p x
    rw [Module.End.mul_apply, plin_apply, plin_apply, plin_apply, pmap_pcls, pmap_pcls, pmap_pcls, map_mul]
    rfl

theorem prep_apply_pcls {Γ : Type*} [Group Γ] (a : Γ →* Monoid.End G) (γ : Γ) (g : G) :
    prep p a γ (pcls p g) = pcls p (a γ g) := by
  show plin p (a γ) (pcls p g) = _
  rw [plin_apply, pmap_pcls]
  rfl

end PMod
p2m_reactivate "P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField.S17C7.PMod"

variable (K : Type u) [Field K]

theorem finrank_eq_natCard_points
    (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B]
    [Finite (WithConv (B →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (B →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : B →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] B →ₐ[AlgebraicClosure K]
            (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))) :
    Module.finrank K B = Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K)) := by
  classical
  letI : Fintype (WithConv (B →ₐ[K] AlgebraicClosure K)) := Fintype.ofFinite _
  let e := LinearEquiv.ofBijective
    (Algebra.TensorProduct.lift
      (Algebra.ofId (AlgebraicClosure K) (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
      (Pi.algHom K _
        fun ν : WithConv (B →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : B →ₐ[K] AlgebraicClosure K))
      (fun _ _ => Commute.all _ _) :
      AlgebraicClosure K ⊗[K] B →ₐ[AlgebraicClosure K]
        (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)).toLinearMap hev
  have h1 : Module.finrank (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] B) = Module.finrank K B :=
    Module.finrank_baseChange
  rw [← h1, e.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

theorem quotient_package
    (n : ℕ) (p : ℕ) (L : IntermediateField K (AlgebraicClosure K))
    (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [Coalgebra.IsCocomm K B]
    [Finite (WithConv (B →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (B →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : B →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] B →ₐ[AlgebraicClosure K]
            (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (htors : ∀ ν : WithConv (B →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1)
    (hL : ∀ (ν : B →ₐ[K] AlgebraicClosure K) (b : B), ν b ∈ L)
    (W : Submonoid (WithConv (B →ₐ[K] AlgebraicClosure K)))
    (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] [Coalgebra.IsCocomm K Ā] [Module.Finite K Ā]
    (π : B →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hpts₁ : ∀ ψ : Ā →ₐ[K] AlgebraicClosure K, WithConv.toConv (ψ.comp (π : B →ₐ[K] Ā)) ∈ W)
    (hpts₂ : ∀ ν ∈ W, ∃ ψ : Ā →ₐ[K] AlgebraicClosure K, ψ.comp (π : B →ₐ[K] Ā) = WithConv.ofConv ν)
    (hrankĀ : Module.finrank K Ā = Nat.card ↥W) :
    ∃ (_ : Finite (WithConv (Ā →ₐ[K] AlgebraicClosure K))),
      Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (Ā →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (Ā →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : Ā →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] Ā →ₐ[AlgebraicClosure K]
            (WithConv (Ā →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) ∧
      Nat.card (WithConv (Ā →ₐ[K] AlgebraicClosure K)) = Nat.card ↥W ∧
      (∀ ν : WithConv (Ā →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1) ∧
      (∀ (ν : Ā →ₐ[K] AlgebraicClosure K) (b : Ā), ν b ∈ L) := by

  have hinj : Function.Injective (fun ψ : WithConv (Ā →ₐ[K] AlgebraicClosure K) =>
      WithConv.toConv ((WithConv.ofConv ψ).comp (π : B →ₐ[K] Ā))) := by
    intro ψ ψ' h
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hπ b
    have := congrArg (fun f : WithConv (B →ₐ[K] AlgebraicClosure K) => WithConv.ofConv f a) h
    simpa using this
  haveI : Finite (WithConv (Ā →ₐ[K] AlgebraicClosure K)) := Finite.of_injective _ hinj
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  ·

    classical
    letI : Fintype (WithConv (B →ₐ[K] AlgebraicClosure K)) := Fintype.ofFinite _
    letI : Fintype (WithConv (Ā →ₐ[K] AlgebraicClosure K)) := Fintype.ofFinite _
    set Ω := AlgebraicClosure K with hΩ

    let resπ : WithConv (Ā →ₐ[K] Ω) → WithConv (B →ₐ[K] Ω) :=
      fun ψ => WithConv.toConv ((WithConv.ofConv ψ).comp (π : B →ₐ[K] Ā))
    have hres_inj : Function.Injective resπ := hinj
    let pull : (WithConv (B →ₐ[K] Ω) → Ω) →ₐ[Ω] (WithConv (Ā →ₐ[K] Ω) → Ω) :=
      Pi.algHom Ω _ fun ψ => Pi.evalAlgHom Ω (fun _ => Ω) (resπ ψ)
    have hpull : Function.Surjective pull := by
      intro φ
      refine ⟨fun ν => if h : ∃ ψ, resπ ψ = ν then φ h.choose else 0, funext fun ψ => ?_⟩
      have h : ∃ ψ', resπ ψ' = resπ ψ := ⟨ψ, rfl⟩
      simp only [pull, Pi.algHom_apply, Pi.evalAlgHom_apply, dif_pos h]
      exact congrArg φ (hres_inj h.choose_spec)
    set evA := Algebra.TensorProduct.lift
        (Algebra.ofId Ω (WithConv (Ā →ₐ[K] Ω) → Ω))
        (Pi.algHom K _ fun ν : WithConv (Ā →ₐ[K] Ω) => (WithConv.ofConv ν : Ā →ₐ[K] Ω))
        (fun _ _ => Commute.all _ _) with hevA
    set evB := Algebra.TensorProduct.lift
        (Algebra.ofId Ω (WithConv (B →ₐ[K] Ω) → Ω))
        (Pi.algHom K _ fun ν : WithConv (B →ₐ[K] Ω) => (WithConv.ofConv ν : B →ₐ[K] Ω))
        (fun _ _ => Commute.all _ _) with hevBdef
    let idπ : Ω ⊗[K] B →ₐ[Ω] Ω ⊗[K] Ā := Algebra.TensorProduct.map (AlgHom.id Ω Ω) (π : B →ₐ[K] Ā)
    have hsq : evA.comp idπ = pull.comp evB := by
      apply Algebra.TensorProduct.ext
      · ext
      · apply AlgHom.ext; intro b; funext ψ
        simp [evA, evB, idπ, pull, resπ, Algebra.TensorProduct.lift_tmul]
    have hidπ : Function.Surjective idπ := by
      have : Function.Surjective ((π : B →ₐ[K] Ā).toLinearMap.lTensor Ω) :=
        LinearMap.lTensor_surjective Ω (by exact hπ)
      intro y; obtain ⟨x, hx⟩ := this y; exact ⟨x, by simp [idπ] at hx ⊢; exact hx⟩
    have hsurj : Function.Surjective evA := by
      intro φ
      obtain ⟨g, hg⟩ := hpull φ
      obtain ⟨x, hx⟩ := hev.2 g
      refine ⟨idπ x, ?_⟩
      have := congrArg (fun f => f x) (congrArg DFunLike.coe hsq)
      simp only [AlgHom.coe_comp, Function.comp_apply] at this
      rw [this, hx, hg]

    have hcardA : Nat.card (WithConv (Ā →ₐ[K] Ω)) = Nat.card ↥W := by
      let φW : WithConv (Ā →ₐ[K] Ω) → ↥W := fun ψ =>
        ⟨WithConv.toConv ((WithConv.ofConv ψ).comp (π : B →ₐ[K] Ā)), hpts₁ (WithConv.ofConv ψ)⟩
      refine Nat.card_eq_of_bijective φW ⟨fun ψ ψ' h => hinj (congrArg Subtype.val h), fun w => ?_⟩
      obtain ⟨ψ, hψ⟩ := hpts₂ w.1 w.2
      refine ⟨WithConv.toConv ψ, Subtype.ext ?_⟩
      show WithConv.toConv ((WithConv.ofConv (WithConv.toConv ψ)).comp (π : B →ₐ[K] Ā)) = (w : WithConv (B →ₐ[K] Ω))
      rw [WithConv.ofConv_toConv, hψ, WithConv.toConv_ofConv]
    have hdim : Module.finrank Ω (Ω ⊗[K] Ā) = Module.finrank Ω (WithConv (Ā →ₐ[K] Ω) → Ω) := by
      rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card, hrankĀ, ← hcardA, Nat.card_eq_fintype_card]
    have hinjA : Function.Injective evA := by
      have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr
        (show Function.Surjective evA.toLinearMap from hsurj)
      exact this
    exact ⟨hinjA, hsurj⟩
  ·
    classical
    let φ : WithConv (Ā →ₐ[K] AlgebraicClosure K) → ↥W := fun ψ =>
      ⟨WithConv.toConv ((WithConv.ofConv ψ).comp (π : B →ₐ[K] Ā)), hpts₁ (WithConv.ofConv ψ)⟩
    refine Nat.card_eq_of_bijective φ ⟨fun ψ ψ' h => hinj (congrArg Subtype.val h), fun w => ?_⟩
    obtain ⟨ψ, hψ⟩ := hpts₂ w.1 w.2
    refine ⟨WithConv.toConv ψ, Subtype.ext ?_⟩
    show WithConv.toConv ((WithConv.ofConv (WithConv.toConv ψ)).comp (π : B →ₐ[K] Ā)) = (w : WithConv (B →ₐ[K] AlgebraicClosure K))
    rw [WithConv.ofConv_toConv, hψ, WithConv.toConv_ofConv]
  ·
    let resπ : WithConv (Ā →ₐ[K] AlgebraicClosure K) →* WithConv (B →ₐ[K] AlgebraicClosure K) :=
      { toFun := fun ψ => WithConv.toConv ((WithConv.ofConv ψ).comp (π : B →ₐ[K] Ā))
        map_one' := by
          apply WithConv.ofConv_injective
          apply AlgHom.ext
          intro b
          rw [WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
          congr 1
          exact CoalgHomClass.counit_comp_apply π b
        map_mul' := fun ψ ψ' => by
          apply WithConv.ofConv_injective
          rw [WithConv.ofConv_toConv, AlgHom.convMul_comp_bialgHom_distrib] }
    have hres : Function.Injective resπ := hinj
    intro ν
    apply hres
    rw [map_pow, map_one]
    exact htors _
  · intro ν b
    obtain ⟨a, rfl⟩ := hπ b
    exact hL ((ν : Ā →ₐ[K] AlgebraicClosure K).comp (π : B →ₐ[K] Ā)) a

set_option maxHeartbeats 3200000 in

theorem exists_submonoid_lineAction
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (P : Subgroup (L ≃ₐ[K] L)) (hPn : P.Normal) (hPp : IsPGroup p ↥P)
    (hcomm : ∀ a b : (L ≃ₐ[K] L), a⁻¹ * b⁻¹ * a * b ∈ P)
    (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [Coalgebra.IsCocomm K B]
    [Finite (WithConv (B →ₐ[K] AlgebraicClosure K))]
    (htors : ∀ ν : WithConv (B →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1)
    (hL : ∀ (ν : B →ₐ[K] AlgebraicClosure K) (b : B), ν b ∈ L)
    (hV : 1 < Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K))) :
    ∃ (W : Submonoid (WithConv (B →ₐ[K] AlgebraicClosure K))),
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, ∀ ν ∈ W, ∀ ν' : WithConv (B →ₐ[K] AlgebraicClosure K),
        (∀ a : B, WithConv.ofConv ν' a = σ (WithConv.ofConv ν a)) → ν' ∈ W) ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (r : ℕ), 0 < r ∧ Fintype.card F = p ^ r ∧
        Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K)) = Nat.card ↥W * p ^ r ∧
        ∃ act : F → WithConv (B →ₐ[K] AlgebraicClosure K) → WithConv (B →ₐ[K] AlgebraicClosure K),
          (∀ a : F, ∀ w ∈ W, act a w ∈ W) ∧
          (∀ (a : F) (f g : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act a (f * g) = act a f * act a g * w) ∧
          (∀ (a b : F) (f : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act (a + b) f = act a f * act b f * w) ∧
          (∀ (a b : F) (f : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act (a * b) f = act a (act b f) * w) ∧
          (∀ f : WithConv (B →ₐ[K] AlgebraicClosure K), ∃ w ∈ W, act 1 f = f * w) ∧
          (∀ f : WithConv (B →ₐ[K] AlgebraicClosure K), act 0 f ∈ W) ∧
          (∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) (f g : WithConv (B →ₐ[K] AlgebraicClosure K)),
            (∀ x : B, WithConv.ofConv g x = σ (WithConv.ofConv f x)) →
            ∃ w ∈ W, ∀ x : B, WithConv.ofConv (act a g * w) x = σ (WithConv.ofConv (act a f) x)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Fact p.Prime := ⟨hp⟩

  let Ω := AlgebraicClosure K
  let Pt := WithConv (B →ₐ[K] AlgebraicClosure K)
  haveI : Fintype Pt := Fintype.ofFinite _
  have hpn : p ^ n ≠ 0 := pow_ne_zero n hp.ne_zero

  have hunit : ∀ f : Pt, IsUnit f := fun f => IsUnit.of_pow_eq_one (htors f) hpn
  let u : Pt → Ptˣ := fun f => (hunit f).unit
  have hu : ∀ f, ((u f : Ptˣ) : Pt) = f := fun f => (hunit f).unit_spec
  have u_mul : ∀ f g, u (f * g) = u f * u g := fun f g => Units.ext (by rw [Units.val_mul, hu, hu, hu])
  have u_one : u 1 = 1 := Units.ext (by rw [hu, Units.val_one])
  have u_coe : ∀ g : Ptˣ, u (g : Pt) = g := fun g => Units.ext (hu _)

  let gal : (L ≃ₐ[K] L) → Pt → Pt := fun γ f =>
    WithConv.toConv (((γ.liftNormal Ω : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp (WithConv.ofConv f))
  have gal_apply : ∀ γ (f : Pt) (b : B),
      WithConv.ofConv (gal γ f) b = algebraMap L Ω (γ ⟨WithConv.ofConv f b, hL _ b⟩) := by
    intro γ f b
    exact AlgEquiv.liftNormal_commutes γ Ω ⟨WithConv.ofConv f b, hL _ b⟩
  have gal_mul_pt : ∀ γ (f g : Pt), gal γ (f * g) = gal γ f * gal γ g := by
    intro γ f g
    show WithConv.toConv (_) = WithConv.toConv _ * WithConv.toConv _
    rw [AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]
  have gal_one_pt : ∀ γ, gal γ 1 = 1 := by
    intro γ
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    show (γ.liftNormal Ω) (WithConv.ofConv (1 : Pt) b) = WithConv.ofConv (1 : Pt) b
    rw [AlgHom.convOne_apply]
    exact AlgEquiv.commutes _ _
  have gal_one : ∀ f, gal 1 f = f := by
    intro f
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    rw [gal_apply]
    rfl
  have gal_mul : ∀ γ δ f, gal (γ * δ) f = gal γ (gal δ f) := by
    intro γ δ f
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    rw [gal_apply, gal_apply, AlgEquiv.mul_apply]
    congr 2
    exact Subtype.ext (gal_apply δ f b).symm
  let galHom : (L ≃ₐ[K] L) → Pt →* Pt := fun γ =>
    { toFun := gal γ, map_one' := gal_one_pt γ, map_mul' := gal_mul_pt γ }
  have galHom_apply : ∀ γ f, galHom γ f = gal γ f := fun _ _ => rfl

  let M := PMod p Ptˣ
  let cls : Pt → M := fun f => pcls p (u f)
  have cls_mul : ∀ f g, cls (f * g) = cls f + cls g := by
    intro f g
    show pcls p (u (f * g)) = _
    rw [u_mul, pcls_mul]
  have cls_one : cls 1 = 0 := by
    show pcls p (u 1) = 0
    rw [u_one, pcls_one]
  have cls_surj : Function.Surjective cls := by
    intro x
    obtain ⟨g, rfl⟩ := pcls_surjective p x
    exact ⟨(g : Pt), by show pcls p (u (g : Pt)) = _; rw [u_coe]⟩
  haveI : Finite M := Finite.of_surjective cls cls_surj

  let aut : (L ≃ₐ[K] L) →* Monoid.End Ptˣ :=
    { toFun := fun γ => Units.map (galHom γ)
      map_one' := by
        apply MonoidHom.ext
        intro g
        apply Units.ext
        show gal 1 (g : Pt) = (g : Pt)
        exact gal_one _
      map_mul' := fun γ δ => by
        apply MonoidHom.ext
        intro g
        apply Units.ext
        show gal (γ * δ) (g : Pt) = gal γ (gal δ (g : Pt))
        exact gal_mul _ _ _ }
  have a_apply : ∀ γ (g : Ptˣ), ((aut γ g : Ptˣ) : Pt) = gal γ (g : Pt) := fun _ _ => rfl
  have ua : ∀ γ (f : Pt), u (gal γ f) = aut γ (u f) := fun γ f => Units.ext (by rw [hu, a_apply, hu])
  let ρ : Representation (ZMod p) (L ≃ₐ[K] L) M := prep p aut
  have ρ_cls : ∀ γ f, ρ γ (cls f) = cls (gal γ f) := by
    intro γ f
    show prep p aut γ (pcls p (u f)) = pcls p (u (gal γ f))
    rw [prep_apply_pcls, ua]

  have hM : ∃ x : M, x ≠ 0 := by
    by_contra hall
    push Not at hall

    have hsurj : ∀ g : Ptˣ, ∃ t : Ptˣ, t ^ p = g := by
      intro g
      have h0 : cls (g : Pt) = cls 1 := by rw [hall (cls (g : Pt)), hall (cls 1)]
      have h1 : pcls p g = pcls p 1 := by
        have : pcls p (u (g : Pt)) = pcls p (u 1) := h0
        rwa [u_coe, u_one] at this
      obtain ⟨t, ht⟩ := (pcls_eq_iff p g 1).mp h1
      refine ⟨t⁻¹, ?_⟩
      rw [inv_pow]
      exact (eq_inv_of_mul_eq_one_left ht.symm).symm
    have hk : ∀ (k : ℕ) (g : Ptˣ), ∃ t : Ptˣ, t ^ p ^ k = g := by
      intro k
      induction k with
      | zero => intro g; exact ⟨g, by rw [pow_zero, pow_one]⟩
      | succ k ih =>
          intro g
          obtain ⟨t, rfl⟩ := ih g
          obtain ⟨s, rfl⟩ := hsurj t
          exact ⟨s, by rw [pow_succ', pow_mul]⟩
    have htriv : ∀ g : Ptˣ, g = 1 := by
      intro g
      obtain ⟨t, rfl⟩ := hk n g
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, htors, Units.val_one])
    have hone : Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => by rw [← hu a, ← hu b, htriv (u a), htriv (u b)]⟩, ⟨1⟩⟩
    rw [hone] at hV
    exact lt_irrefl 1 hV
  haveI : Nontrivial M := by
    obtain ⟨x, hx⟩ := hM
    exact ⟨⟨x, 0, hx⟩⟩

  haveI := hPn
  obtain ⟨Wb, hWbstab, hWbne, F, instF, instFin, instModF, r, hr, hF, hsmulnat, hfin1, hscalar⟩ :=
    Representation.exists_submodule_quotient_line_of_commutator_le_of_isPGroup p P hPp hcomm ρ

  let W : Submonoid Pt :=
    { carrier := {f | cls f ∈ Wb}
      one_mem' := by
        simp only [Set.mem_setOf_eq, cls_one]
        exact Wb.zero_mem
      mul_mem' := fun {f g} hf hg => by
        simp only [Set.mem_setOf_eq] at hf hg ⊢
        rw [cls_mul]; exact Wb.add_mem hf hg }
  have memW : ∀ f, f ∈ W ↔ cls f ∈ Wb := fun _ => Iff.rfl
  let q : Pt → M ⧸ Wb := fun f => Wb.mkQ (cls f)
  have q_apply : ∀ f, q f = Wb.mkQ (cls f) := fun _ => rfl
  have q_mul : ∀ f g, q (f * g) = q f + q g := by
    intro f g; rw [q_apply, cls_mul, map_add]
  have q_surj : Function.Surjective q :=
    (Submodule.mkQ_surjective Wb).comp cls_surj
  have q_W : ∀ w ∈ W, q w = 0 := fun w hw => (Submodule.Quotient.mk_eq_zero Wb).mpr hw
  have q_eq_zero_iff : ∀ f, q f = 0 ↔ f ∈ W := fun f => Submodule.Quotient.mk_eq_zero Wb

  have hdiv : ∀ f g : Pt, f * (((u f)⁻¹ * u g : Ptˣ) : Pt) = g := by
    intro f g
    calc f * (((u f)⁻¹ * u g : Ptˣ) : Pt) = ((u f : Ptˣ) : Pt) * (((u f)⁻¹ * u g : Ptˣ) : Pt) := by rw [hu]
      _ = ((u f * ((u f)⁻¹ * u g) : Ptˣ) : Pt) := (Units.val_mul _ _).symm
      _ = ((u g : Ptˣ) : Pt) := by rw [mul_inv_cancel_left]
      _ = g := hu g
  have cls_div : ∀ f g : Pt, cls ((((u f)⁻¹ * u g : Ptˣ) : Pt)) + cls f = cls g := by
    intro f g
    rw [← cls_mul, mul_comm, hdiv]
  have q_div : ∀ f g : Pt, q ((((u f)⁻¹ * u g : Ptˣ) : Pt)) + q f = q g := by
    intro f g
    rw [q_apply, q_apply, q_apply, ← map_add, cls_div]
  have q_eq_imp : ∀ f g, q f = q g → ∃ w ∈ W, g = f * w := by
    intro f g h
    refine ⟨(((u f)⁻¹ * u g : Ptˣ) : Pt), ?_, (hdiv f g).symm⟩
    rw [← q_eq_zero_iff]
    have h2 := q_div f g
    rw [h] at h2
    exact add_eq_right.mp h2
  have q_mulW : ∀ f, ∀ w ∈ W, q (f * w) = q f := by
    intro f w hw; rw [q_mul, q_W w hw, add_zero]

  haveI : Fintype (M ⧸ Wb) := Fintype.ofFinite _
  have hcardQ : Fintype.card (M ⧸ Wb) = p ^ r := by
    haveI : Module.Finite F (M ⧸ Wb) := Module.Finite.of_finite
    rw [Module.card_eq_pow_finrank (K := F) (V := M ⧸ Wb), hfin1, pow_one, hF]
  obtain ⟨sq, hsq⟩ : ∃ sq : M ⧸ Wb → Pt, ∀ c, q (sq c) = c := ⟨fun c => Classical.choose (q_surj c),
    fun c => Classical.choose_spec (q_surj c)⟩
  have hcard : Nat.card Pt = Nat.card ↥W * p ^ r := by
    let e : Pt → (M ⧸ Wb) × ↥W := fun f =>
      ⟨q f, ⟨(((u (sq (q f)))⁻¹ * u f : Ptˣ) : Pt), by
        rw [← q_eq_zero_iff]
        have h2 := q_div (sq (q f)) f
        rw [hsq] at h2
        exact add_eq_right.mp h2⟩⟩
    have he : Function.Bijective e := by
      refine ⟨fun f g h => ?_, fun ⟨c, w⟩ => ?_⟩
      · have h1 : q f = q g := congrArg Prod.fst h
        have h2 : ((((u (sq (q f)))⁻¹ * u f : Ptˣ) : Pt)) = ((((u (sq (q g)))⁻¹ * u g : Ptˣ) : Pt)) :=
          congrArg (fun x => ((x.2 : ↥W) : Pt)) h
        rw [← hdiv (sq (q f)) f, ← hdiv (sq (q g)) g, h2, h1]
      · refine ⟨sq c * (w : Pt), ?_⟩
        have hq : q (sq c * (w : Pt)) = c := by rw [q_mulW _ _ w.2, hsq]
        apply Prod.ext
        · exact hq
        · apply Subtype.ext
          show (((u (sq (q (sq c * (w : Pt)))))⁻¹ * u (sq c * (w : Pt)) : Ptˣ) : Pt) = (w : Pt)
          rw [hq, u_mul, inv_mul_cancel_left, hu]
    rw [Nat.card_eq_of_bijective e he, Nat.card_prod, Nat.card_eq_fintype_card, hcardQ, mul_comm]

  let act : F → Pt → Pt := fun a f => Classical.choose (q_surj (a • q f))
  have act_spec : ∀ a f, q (act a f) = a • q f := fun a f => Classical.choose_spec (q_surj (a • q f))

  have gal_restrict : ∀ (σ : Ω ≃ₐ[K] Ω), ∃ γ : L ≃ₐ[K] L,
      (∀ y : L, algebraMap L Ω (γ y) = σ (algebraMap L Ω y)) ∧
      ∀ (f g : Pt), (∀ x : B, WithConv.ofConv g x = σ (WithConv.ofConv f x)) → g = gal γ f := by
    intro σ
    refine ⟨σ.restrictNormal L, AlgEquiv.restrictNormal_commutes σ L, fun f g hfg => ?_⟩
    apply WithConv.ofConv_injective
    apply AlgHom.ext
    intro b
    rw [hfg, gal_apply, AlgEquiv.restrictNormal_commutes]
    rfl
  have q_gal : ∀ γ, ∃ c : F, ∀ f, q (gal γ f) = c • q f := by
    intro γ
    obtain ⟨c, hc⟩ := hscalar γ
    exact ⟨c, fun f => by rw [q_apply, q_apply, ← ρ_cls]; exact hc (cls f)⟩
  refine ⟨W, ?_, F, instF, instFin, r, hr, hF, hcard, act, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro σ ν hν ν' hν'
    obtain ⟨γ, -, hγ⟩ := gal_restrict σ
    rw [hγ ν ν' hν', memW, ← ρ_cls]
    exact hWbstab _ _ hν
  · intro a w hw
    rw [← q_eq_zero_iff, act_spec a w, q_W w hw]
    exact smul_zero a
  · intro a f g
    apply q_eq_imp
    rw [q_mul, act_spec a f, act_spec a g, act_spec a (f * g), q_mul]
    exact (smul_add a (q f) (q g)).symm
  · intro a b f
    apply q_eq_imp
    rw [q_mul, act_spec a f, act_spec b f, act_spec (a + b) f]
    exact (add_smul a b (q f)).symm
  · intro a b f
    apply q_eq_imp
    rw [act_spec a, act_spec b f, act_spec (a * b) f]
    exact (mul_smul a b (q f)).symm
  · intro f
    apply q_eq_imp
    rw [act_spec 1 f]
    exact (one_smul F (q f)).symm
  · intro f
    rw [← q_eq_zero_iff, act_spec 0 f]
    exact zero_smul F (q f)
  · intro σ a f g hfg
    obtain ⟨γ, hγv, hγ⟩ := gal_restrict σ
    have hg : g = gal γ f := hγ f g hfg
    obtain ⟨c, hc⟩ := q_gal γ
    have e1 : q (act a g) = (a * c) • q f := by rw [act_spec a g, hg, hc f, smul_smul]
    have e2 : q (gal γ (act a f)) = (a * c) • q f := by rw [hc (act a f), act_spec a f, smul_smul, mul_comm]
    obtain ⟨w, hw, hgal⟩ : ∃ w ∈ W, gal γ (act a f) = act a g * w := q_eq_imp _ _ (e1.trans e2.symm)
    refine ⟨w, hw, fun x => ?_⟩
    rw [← hgal, gal_apply, hγv]
    rfl

theorem exists_fVectStructure_of_pointAction [PerfectField K]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] [Coalgebra.IsCocomm K H]
    [Finite (WithConv (H →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (H →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : H →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] H →ₐ[AlgebraicClosure K]
            (WithConv (H →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (F : Type) [Field F] [Fintype F]
    (smulF : F → WithConv (H →ₐ[K] AlgebraicClosure K) → WithConv (H →ₐ[K] AlgebraicClosure K))
    (h_one : ∀ x, smulF 1 x = x)
    (h_mul : ∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x))
    (h_zero : ∀ x, smulF 0 x = 1)
    (h_add : ∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x)
    (h_pt_one : ∀ a : F, smulF a 1 = 1)
    (h_pt_mul : ∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y)
    (h_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) (x y : WithConv (H →ₐ[K] AlgebraicClosure K)),
        (∀ h : H, WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
        ∀ h : H, WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h)) :
    ∃ σF : HopfAlgebra.FVectStructure F K H,
      ∀ (a : F) (x : WithConv (H →ₐ[K] AlgebraicClosure K)),
        WithConv.toConv ((WithConv.ofConv x).comp (σF.act a : H →ₐ[K] H)) = smulF a x :=
  HopfAlgebra.exists_fVectStructure_of_pointAction_of_bijective_evalPoints K H hev F smulF
    h_one h_mul h_zero h_add h_pt_one h_pt_mul h_gal

theorem bijective_evalPoints_hopfKer
    (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [Coalgebra.IsCocomm K B]
    [Finite (WithConv (B →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (B →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : B →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] B →ₐ[AlgebraicClosure K]
            (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (W : Submonoid (WithConv (B →ₐ[K] AlgebraicClosure K)))
    (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] (π : B →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker₁ : ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (B →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h)
    (hker₂ : ∀ ν ν' : WithConv (B →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w)
    (hrankK : Module.finrank K ↥(HopfAlgebra.hopfKer π) * Nat.card ↥W = Module.finrank K B) :
    ∃ (_ : Finite (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))),
      Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] ↥(HopfAlgebra.hopfKer π) →ₐ[AlgebraicClosure K]
            (WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) :=
  HopfAlgebra.bijective_evalPoints_hopfKer_of_bijective_evalPoints K B hev W Ā π hπ hker₁ hker₂ hrankK

theorem transport_lineAction
    (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [Coalgebra.IsCocomm K B]
    (W : Submonoid (WithConv (B →ₐ[K] AlgebraicClosure K)))
    (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] (π : B →ₐc[K] Ā)
    (hker₁ : ∀ h : ↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K,
        ∃ ν : WithConv (B →ₐ[K] AlgebraicClosure K), (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = h)
    (hker₂ : ∀ ν ν' : WithConv (B →ₐ[K] AlgebraicClosure K),
        (WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val = (WithConv.ofConv ν').comp (HopfAlgebra.hopfKer π).val
          ↔ ∃ w ∈ W, ν' = ν * w)
    (p n : ℕ) (hpn : p ^ n ≠ 0) (htors : ∀ ν : WithConv (B →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1)
    (F : Type) [Field F] [Fintype F]
    (act : F → WithConv (B →ₐ[K] AlgebraicClosure K) → WithConv (B →ₐ[K] AlgebraicClosure K))
    (hW : ∀ a : F, ∀ w ∈ W, act a w ∈ W)
    (h_pt_mul : ∀ (a : F) (f g : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act a (f * g) = act a f * act a g * w)
    (h_add : ∀ (a b : F) (f : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act (a + b) f = act a f * act b f * w)
    (h_mul : ∀ (a b : F) (f : WithConv (B →ₐ[K] AlgebraicClosure K)), ∃ w ∈ W, act (a * b) f = act a (act b f) * w)
    (h_one : ∀ f : WithConv (B →ₐ[K] AlgebraicClosure K), ∃ w ∈ W, act 1 f = f * w)
    (h_zero : ∀ f : WithConv (B →ₐ[K] AlgebraicClosure K), act 0 f ∈ W)
    (h_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) (f g : WithConv (B →ₐ[K] AlgebraicClosure K)),
        (∀ x : B, WithConv.ofConv g x = σ (WithConv.ofConv f x)) →
        ∃ w ∈ W, ∀ x : B, WithConv.ofConv (act a g * w) x = σ (WithConv.ofConv (act a f) x)) :
    ∃ smulF : F → WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K),
      (∀ x, smulF 1 x = x) ∧
      (∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x)) ∧
      (∀ x, smulF 0 x = 1) ∧
      (∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x) ∧
      (∀ a : F, smulF a 1 = 1) ∧
      (∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y) ∧
      (∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F) (x y : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K)),
        (∀ h : ↥(HopfAlgebra.hopfKer π), WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
        ∀ h : ↥(HopfAlgebra.hopfKer π), WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h)) := by
  classical

  let res : WithConv (B →ₐ[K] AlgebraicClosure K) →* WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) :=
    { toFun := fun ν => WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val)
      map_one' := by
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro h
        rw [WithConv.ofConv_toConv, AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
        rfl
      map_mul' := fun ν ν' => by
        apply WithConv.ofConv_injective
        rw [WithConv.ofConv_toConv]
        exact AlgHom.convMul_comp_bialgHom_distrib ν ν' (HopfAlgebra.hopfKerVal π) }
  have res_apply : ∀ ν, res ν = WithConv.toConv ((WithConv.ofConv ν).comp (HopfAlgebra.hopfKer π).val) :=
    fun _ => rfl
  have res_coe : ∀ ν (h : ↥(HopfAlgebra.hopfKer π)), WithConv.ofConv (res ν) h = WithConv.ofConv ν (h : B) :=
    fun _ _ => rfl

  have res_eq_iff : ∀ ν ν', res ν = res ν' ↔ ∃ w ∈ W, ν' = ν * w := by
    intro ν ν'
    rw [← hker₂, res_apply, res_apply]
    exact ⟨fun h => congrArg WithConv.ofConv h, fun h => congrArg WithConv.toConv h⟩
  have res_W : ∀ w ∈ W, res w = 1 := by
    intro w hw
    rw [← map_one res, eq_comm, res_eq_iff]
    exact ⟨w, hw, (one_mul w).symm⟩
  have res_mulW : ∀ ν, ∀ w ∈ W, res (ν * w) = res ν :=
    fun ν w hw => ((res_eq_iff ν (ν * w)).mpr ⟨w, hw, rfl⟩).symm
  have res_surj : Function.Surjective res := by
    intro x
    obtain ⟨ν, hν⟩ := hker₁ (WithConv.ofConv x)
    exact ⟨ν, by rw [res_apply, hν, WithConv.toConv_ofConv]⟩

  have res_unit : ∀ x : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K), IsUnit x := by
    intro x
    obtain ⟨ν, rfl⟩ := res_surj x
    exact IsUnit.of_pow_eq_one (by rw [← map_pow, htors, map_one]) hpn

  let sec : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) → WithConv (B →ₐ[K] AlgebraicClosure K) :=
    fun x => Classical.choose (res_surj x)
  have sec_spec : ∀ x, res (sec x) = x := fun x => Classical.choose_spec (res_surj x)
  let smulF : F → WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) →
      WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K) := fun a x => res (act a (sec x))
  have smulF_def : ∀ a x, smulF a x = res (act a (sec x)) := fun _ _ => rfl

  have key : ∀ (a : F) (ν : WithConv (B →ₐ[K] AlgebraicClosure K)), smulF a (res ν) = res (act a ν) := by
    intro a ν
    rw [smulF_def]
    obtain ⟨w, hw, hsec⟩ := (res_eq_iff ν (sec (res ν))).mp (sec_spec (res ν)).symm
    rw [hsec]
    obtain ⟨w₁, hw₁, h1⟩ := h_pt_mul a ν w
    rw [h1, res_mulW _ w₁ hw₁, res_mulW _ (act a w) (hW a w hw)]
  have l_one : ∀ x, smulF 1 x = x := by
    intro x
    obtain ⟨ν, rfl⟩ := res_surj x
    obtain ⟨w, hw, h⟩ := h_one ν
    rw [key 1 ν, h, res_mulW ν w hw]
  have l_mul : ∀ (a b : F) x, smulF (a * b) x = smulF a (smulF b x) := by
    intro a b x
    obtain ⟨ν, rfl⟩ := res_surj x
    obtain ⟨w, hw, h⟩ := h_mul a b ν
    rw [key b ν, key a (act b ν), key (a * b) ν, h, res_mulW _ w hw]
  have l_zero : ∀ x, smulF 0 x = 1 := by
    intro x
    obtain ⟨ν, rfl⟩ := res_surj x
    rw [key 0 ν, res_W _ (h_zero ν)]
  have l_add : ∀ (a b : F) x, smulF (a + b) x = smulF a x * smulF b x := by
    intro a b x
    obtain ⟨ν, rfl⟩ := res_surj x
    obtain ⟨w, hw, h⟩ := h_add a b ν
    rw [key a ν, key b ν, key (a + b) ν, h, res_mulW _ w hw, map_mul]
  have l_pt_mul : ∀ (a : F) x y, smulF a (x * y) = smulF a x * smulF a y := by
    intro a x y
    obtain ⟨ν, rfl⟩ := res_surj x
    obtain ⟨ν', rfl⟩ := res_surj y
    obtain ⟨w, hw, h⟩ := h_pt_mul a ν ν'
    rw [key a ν, key a ν', ← map_mul, key a (ν * ν'), h, res_mulW _ w hw, map_mul]
  have l_pt_one : ∀ a : F, smulF a 1 = 1 := by
    intro a
    have e1 : smulF a 1 = res (act a 1) := by
      have := key a 1
      rw [map_one] at this
      exact this
    obtain ⟨w, hw, h⟩ := h_pt_mul a 1 1
    rw [mul_one] at h
    have e2 : res (act a 1) * res (act a 1) = res (act a 1) := by
      conv_rhs => rw [h]
      rw [res_mulW _ w hw, map_mul]
    obtain ⟨u, hu⟩ := res_unit (res (act a 1))
    have e3 : u * u = u := Units.ext (by rw [Units.val_mul, hu, e2])
    have e4 : u = 1 := mul_eq_left.mp e3
    rw [e1, ← hu]
    exact (congrArg Units.val e4).trans Units.val_one
  have l_gal : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (a : F)
      (x y : WithConv (↥(HopfAlgebra.hopfKer π) →ₐ[K] AlgebraicClosure K)),
      (∀ h : ↥(HopfAlgebra.hopfKer π), WithConv.ofConv y h = σ (WithConv.ofConv x h)) →
      ∀ h : ↥(HopfAlgebra.hopfKer π), WithConv.ofConv (smulF a y) h = σ (WithConv.ofConv (smulF a x) h) := by
    intro σ a x y hxy h
    obtain ⟨ν, rfl⟩ := res_surj x

    let ν' : WithConv (B →ₐ[K] AlgebraicClosure K) :=
      WithConv.toConv (((σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AlgebraicClosure K →ₐ[K] AlgebraicClosure K).comp (WithConv.ofConv ν))
    have hν' : ∀ b : B, WithConv.ofConv ν' b = σ (WithConv.ofConv ν b) := fun _ => rfl
    have hy : y = res ν' := by
      apply WithConv.ofConv_injective
      apply AlgHom.ext
      intro k
      rw [hxy k, res_coe, res_coe, hν']
    obtain ⟨w, hw, hgal⟩ := h_gal σ a ν ν' hν'
    rw [hy, key a ν', key a ν, ← res_mulW (act a ν') w hw, res_coe, res_coe]
    exact hgal (h : B)
  exact ⟨smulF, l_one, l_mul, l_zero, l_add, l_pt_one, l_pt_mul, l_gal⟩

end S17C7
p2m_reactivate "P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField.S17C7.PMod P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField.S17C7"

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] (K : Type u) [Field K] [PerfectField K] [Algebra R K]
    (p : ℕ) [Fact p.Prime] (N n : ℕ)
    (hT : ∀ s : ℕ, 0 < s → s ≤ N → ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = p ^ s →
      IsUnit ((p ^ s : R) - 1) ∧
        ∃ (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R),
          ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)
    (A : Type v) [CommRing A] [HopfAlgebra K A] [Module.Finite K A] [Coalgebra.IsCocomm K A]
    [Finite (WithConv (A →ₐ[K] AlgebraicClosure K))]
    (hev : Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure K) (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
        (Pi.algHom K _
          fun ν : WithConv (A →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : A →ₐ[K] AlgebraicClosure K))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure K ⊗[K] A →ₐ[AlgebraicClosure K]
          (WithConv (A →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)))
    (hcard : Nat.card (WithConv (A →ₐ[K] AlgebraicClosure K)) ≤ p ^ N)
    (htors : ∀ ν : WithConv (A →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1)
    (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L] [IsGalois K L]
    (hL : ∀ (ν : A →ₐ[K] AlgebraicClosure K) (a : A), ν a ∈ L)
    (hΓ : ∃ P : Subgroup (L ≃ₐ[K] L), P.Normal ∧ IsPGroup p ↥P ∧
      ∀ a b : (L ≃ₐ[K] L), a⁻¹ * b⁻¹ * a * b ∈ P) :
    HopfAlgebra.HasFVectDevissage R K p A := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨P, hPnormal, hPgrp, hcomm⟩ := hΓ

  suffices key : ∀ (m : ℕ) (B : Type v) [CommRing B] [HopfAlgebra K B] [Module.Finite K B] [Coalgebra.IsCocomm K B]
      [Finite (WithConv (B →ₐ[K] AlgebraicClosure K))],
      Function.Bijective
        (Algebra.TensorProduct.lift
          (Algebra.ofId (AlgebraicClosure K) (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K))
          (Pi.algHom K _
            fun ν : WithConv (B →ₐ[K] AlgebraicClosure K) => (WithConv.ofConv ν : B →ₐ[K] AlgebraicClosure K))
          (fun _ _ => Commute.all _ _) :
          AlgebraicClosure K ⊗[K] B →ₐ[AlgebraicClosure K]
            (WithConv (B →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K)) →
      Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K)) = m → m ≤ p ^ N →
      (∀ ν : WithConv (B →ₐ[K] AlgebraicClosure K), ν ^ p ^ n = 1) →
      (∀ (ν : B →ₐ[K] AlgebraicClosure K) (b : B), ν b ∈ L) →
      HopfAlgebra.HasFVectDevissage R K p B by
    exact key _ A hev rfl hcard htors hL
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro B _ _ _ _ _ hevB hm hmN htorsB hLB
    have hrankB : Module.finrank K B = m := (S17C7.finrank_eq_natCard_points K B hevB).trans hm
    by_cases hm1 : m = 1
    · exact HopfAlgebra.HasFVectDevissage.nil B (hrankB.trans hm1)
    ·

      have hV1 : 1 < Nat.card (WithConv (B →ₐ[K] AlgebraicClosure K)) := by
        rw [hm]
        have h0 : m ≠ 0 := by
          rw [← hm]
          haveI : Nonempty (WithConv (B →ₐ[K] AlgebraicClosure K)) := ⟨1⟩
          exact Nat.card_pos.ne'
        omega
      obtain ⟨W, hWstab, F, instF, instFin, r, hr, hF, hcardVW, act, hWact, ha_pt_mul, ha_add, ha_mul, ha_one,
          ha_zero, ha_gal⟩ :=
        S17C7.exists_submonoid_lineAction K p n L P hPnormal hPgrp hcomm B htorsB hLB hV1

      obtain ⟨Ā, _, _, _, _, π, hπ, hpts₁, hpts₂, hrankĀ, hker₁, hker₂, hrankK⟩ :=
        HopfAlgebra.exists_bialgHom_surjective_points_eq_of_submonoid_of_bijective_evalPoints_of_perfectField K B hevB W hWstab

      have hW0 : Nat.card ↥W ≠ 0 := by
        haveI : Finite ↥W := Subtype.finite
        exact Nat.card_pos.ne'
      have hrank : Module.finrank K ↥(HopfAlgebra.hopfKer π) = p ^ r := by
        have h := hrankK
        rw [hrankB, ← hm, hcardVW] at h

        rw [mul_comm] at h
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hW0) h

      have hrN : r ≤ N := by
        have h1 : p ^ r ≤ m := by
          rw [← hm, hcardVW]
          exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hW0)
        exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (le_trans h1 hmN)

      obtain ⟨hq, χ, ι, hχ⟩ := hT r hr hrN F hF

      obtain ⟨smulF, hs_one, hs_mul, hs_zero, hs_add, hs_pt_one, hs_pt_mul, hs_gal⟩ :=
        S17C7.transport_lineAction K B W Ā π hker₁ hker₂ p n (pow_ne_zero n hp.ne_zero) htorsB F act hWact
          ha_pt_mul ha_add ha_mul ha_one ha_zero ha_gal
      obtain ⟨instFinK, hevK⟩ := S17C7.bijective_evalPoints_hopfKer K B hevB W Ā π hπ hker₁ hker₂ hrankK
      obtain ⟨σF, -⟩ := S17C7.exists_fVectStructure_of_pointAction K (↥(HopfAlgebra.hopfKer π)) hevK F smulF
        hs_one hs_mul hs_zero hs_add hs_pt_one hs_pt_mul hs_gal

      obtain ⟨instFinĀ, hevĀ, hcardĀ, htorsĀ, hLĀ⟩ :=
        S17C7.quotient_package K n p L B hevB htorsB hLB W Ā π hπ hpts₁ hpts₂ hrankĀ
      have hlt : Nat.card ↥W < m := by
        rw [← hm, hcardVW]
        have h2 : 1 < p ^ r := Nat.one_lt_pow hr.ne' hp.one_lt
        exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero hW0) h2
      have hĀ : HopfAlgebra.HasFVectDevissage R K p Ā :=
        ih (Nat.card ↥W) hlt Ā hevĀ hcardĀ (le_trans hlt.le hmN) htorsĀ hLĀ
      haveI : NeZero r := ⟨hr.ne'⟩
      exact HopfAlgebra.HasFVectDevissage.step B Ā π hπ r F hF hq χ ι hχ hrank σF hĀ

end S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField
end P2MW
export P2MW.S_HopfAlgebra_hasFVectDevissage_of_bijective_evalPoints_of_isPGroup_of_commutator_le_of_perfectField (solution)
