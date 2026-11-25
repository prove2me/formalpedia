-- Prove2me | solution 1 for GlobalTheory.CharGerm.exists_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:19.0198+00:00
-- url     : https://prove2.me/submissions/2afe31ed-12d8-4dbc-8a8c-51d37b407358

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSeriesOfTorsionCharacters
import Theorems.Thm_GlobalTheory_CharGerm_pow_eq_smul
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CharGerm
variable {R₀ : Type} [CommRing R₀] {G : Over (Spec (CommRingCat.of R₀))} [GrpObj G] {g : ℕ}
  {x : ∀ (S : Type) [CommRing S] [Algebra R₀ S], (Fin g → S) → (sp (R₀ := R₀) S ⟶ G)}
  (h0 : ∀ (S : Type) [CommRing S] [Algebra R₀ S], x S 0 = 1)
  (hnat : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (φ : S →ₐ[R₀] S') (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
      spMap φ ≫ x S a = x S' (fun i => φ (a i)))
  (hinj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → x S a = x S b → a = b)
  (hsurj : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (S' : Type) [CommRing S'] [Algebra R₀ S']
    (ρ : S →ₐ[R₀] S'), Function.Surjective ρ → (∀ a ∈ RingHom.ker ρ, IsNilpotent a) →
      ∀ z : sp (R₀ := R₀) S ⟶ G, spMap ρ ≫ z = 1 →
        ∃ a : Fin g → S, (∀ i, a i ∈ RingHom.ker ρ) ∧ z = x S a)
include h0 hnat hinj hsurj
namespace GlobalTheory.CharGerm
theorem _root_.solution (p : ℕ) {S : Type} [CommRing S] [Algebra R₀ S] (hp : IsNilpotent (p : S))
    {a : Fin g → S} (ha : ∀ i, IsNilpotent (a i)) : ∃ N : ℕ, x S a ^ (p ^ N) = 1 := by
  have hle : Ideal.span (Set.range a) ≤ nilradical S := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ha i
  have hI : IsNilpotent (Ideal.span (Set.range a)) :=
    (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 hle
  refine Ideal.IsNilpotent.induction_on
    (P := fun S _ I => ∀ [Algebra R₀ S], IsNilpotent (p : S) → (∀ u ∈ I, IsNilpotent u) →
      ∀ a : Fin g → S, (∀ i, a i ∈ I) → ∃ N : ℕ, x S a ^ (p ^ N) = 1) _ hI ?_ ?_ hp hle a
      (fun i => Ideal.subset_span ⟨i, rfl⟩)
  · intro S _ I hI _ ⟨N, hN⟩ _ a ha
    refine ⟨N, ?_⟩
    rw [pow_eq_smul h0 hnat hinj hsurj hI ha, Nat.cast_pow, hN]
    simp only [zero_mul]
    exact h0 S
  · intro S _ I J hIJ h₁ h₂ _ hp hJ a ha
    obtain ⟨N, hN⟩ := h₂ (by simpa using hp.map (Ideal.Quotient.mk I)) (fun u hu => by
        obtain ⟨v, hv, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hu
        exact (hJ v hv).map _)
      (fun i => Ideal.Quotient.mk I (a i)) (fun i => Ideal.mem_map_of_mem _ (ha i))
    have hk : ∀ u ∈ RingHom.ker (Ideal.Quotient.mkₐ R₀ I), u ∈ I := fun u hu =>
      Ideal.Quotient.eq_zero_iff_mem.1 hu
    obtain ⟨c, hc, hx⟩ := hsurj S _ (Ideal.Quotient.mkₐ R₀ I) Ideal.Quotient.mk_surjective
      (fun u hu => hJ u (hIJ (hk u hu))) (x S a ^ (p ^ N)) (by
        rw [MonObj.comp_pow, hnat _ _ _ _ (fun i => hJ _ (ha i))]
        exact hN)
    obtain ⟨M, hM⟩ := h₁ hp (fun u hu => hJ u (hIJ hu)) c (fun i => hk _ (hc i))
    exact ⟨N + M, by rw [pow_add, pow_mul, hx, hM]⟩
end GlobalTheory.CharGerm
