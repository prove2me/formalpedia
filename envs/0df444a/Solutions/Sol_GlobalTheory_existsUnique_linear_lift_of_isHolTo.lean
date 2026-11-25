-- Prove2me | solution 1 for GlobalTheory.existsUnique_linear_lift_of_isHolTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:13.412027+00:00
-- url     : https://prove2.me/submissions/54c1765b-d1ab-454b-bdfc-29fc9b1f266b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Theorems.Thm_GlobalTheory_existsUnique_linear_lift_of_separating
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_isDiff_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_mem_iff
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open Filter Topology Set Metric
open GlobalTheory
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TangentOrigin
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g m : ℕ)
      (u : HolUnif A L g), (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
      (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
      ∀ G : (Fin m → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ z w, G (z + w) = G z * G w) →
      IsHolTo (Set.univ : Set (Fin m → ℂ)) (fun z => (G z).left) →
      ∃! F : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = G z := by
  intro A _ _ L g m u h₁ h₂ G hG hhol
  letI : CommGroup (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    { (inferInstance : Group (𝟙_ (Over (Sp ℂ)) ⟶ A)) with
      mul_comm := fun a b ↦ by
        obtain ⟨z, rfl⟩ := u.ex_onto a
        obtain ⟨w, rfl⟩ := u.ex_onto b
        exact (u.ex_add z w).symm.trans ((congrArg u.ex (add_comm z w)).trans (u.ex_add w z)) }
  let ex : (Fin g → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (u.ex z)) u.ex_add
  let G' : (Fin m → ℂ) →+ Additive (𝟙_ (Over (Sp ℂ)) ⟶ A) :=
    AddMonoidHom.mk' (fun z ↦ Additive.ofMul (G z)) hG
  let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
  have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q ↦
    Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := (u.ex 0).left pt) (U := ⊤)
    (Set.mem_univ _)
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
    intro q _
    rw [hsub q]
    exact hpU
  have hker : (ex.ker : Set (Fin g → ℂ)) = u.Λ := Set.ext fun z ↦ u.ker z
  refine existsUnique_linear_lift_of_separating (ex := ex) (G := G') u.ex_onto
    (hker ▸ isDiscrete_iff_discreteTopology.2 u.discrete)
    (S := {a | ⊤ ≤ (Additive.toMul a).left ⁻¹ᵁ U})
    (f := fun (s : Γ(A.left, U)) a ↦ valAt' (Additive.toMul a).left U s)
    ?_ ?_ (u.hol U 0).1 ?_ (fun s ↦ (u.hol U s).2) ?_ ?_
  · rw [← map_zero ex]
    exact h0
  · intro a ha b hb h
    refine Over.OverMorphism.ext (f := Additive.toMul a) (g := Additive.toMul b)
      (ext_evalPt (R := ℂ) hU ha hb (RingHom.ext fun s ↦ ?_))
    exact (valAt'_eq_evalPt _ U ha s).symm.trans ((h s).trans (valAt'_eq_evalPt _ U hb s))
  · have := (hhol U 0).1
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro s
    have := (hhol U s).2
    simp only [Set.mem_univ, true_and] at this
    exact this
  · intro w hw
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h₂ w
    have hvU := (tangent_mem_iff (u := u) hv U).2 h0
    refine (h₁ v hv).unique hd ((isDiff_iff hv hU hvU h0 0).2 ?_)
    rw [(isDiff_iff hv hU hvU h0 w).1 hd]
    refine RingHom.ext fun s ↦ TrivSqZeroExt.ext rfl ?_
    rw [jet_snd, jet_snd, map_zero]
    exact hw s
end GlobalTheory
