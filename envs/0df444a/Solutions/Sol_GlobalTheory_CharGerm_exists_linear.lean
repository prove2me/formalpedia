-- Prove2me | solution 1 for GlobalTheory.CharGerm.exists_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:01:32.242352+00:00
-- url     : https://prove2.me/submissions/990cfd4d-3d7d-44fc-8efc-cbf0fb87de2b

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
include h0 hnat hsurj
namespace GlobalTheory.CharGerm
theorem _root_.solution : ∃ d : Fin g → (Fin g ⊕ Fin g → R₀),
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (c : Fin g ⊕ Fin g → S), (∀ k l, c k * c l = 0) →
      x S (fun i => c (Sum.inl i)) * x S (fun i => c (Sum.inr i)) =
        x S (fun i => ∑ k, d i k • c k) := by
  let T := TrivSqZeroExt R₀ (Fin g ⊕ Fin g → R₀)
  let e : Fin g ⊕ Fin g → T := fun k => TrivSqZeroExt.inr (Pi.single k 1)
  have hnil : ∀ v : Fin g ⊕ Fin g → R₀, IsNilpotent (TrivSqZeroExt.inr v : T) := fun v =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  have hker : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom R₀ R₀ (Fin g ⊕ Fin g → R₀)),
      a = TrivSqZeroExt.inr a.snd := fun a ha => by
    ext1
    · exact ha
    · rfl
  obtain ⟨d, hd, hx⟩ := hsurj T R₀ (TrivSqZeroExt.fstHom R₀ R₀ (Fin g ⊕ Fin g → R₀))
    (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩) (fun a ha => by rw [hker a ha]; exact hnil _)
    (x T (fun i => e (Sum.inl i)) * x T (fun i => e (Sum.inr i))) (by
      rw [MonObj.comp_mul, hnat _ _ _ _ (fun i => hnil _), hnat _ _ _ _ (fun i => hnil _)]
      exact (congrArg₂ (· * ·) (h0 R₀) (h0 R₀)).trans (_root_.mul_one _))
  refine ⟨fun i => (d i).snd, fun S _ _ c hc => ?_⟩
  let φ : T →ₐ[R₀] S := TrivSqZeroExt.liftEquivOfComm
    ⟨Fintype.linearCombination R₀ c, fun v w => by
      simp only [Fintype.linearCombination_apply, Finset.sum_mul_sum, smul_mul_smul_comm, hc,
        smul_zero, Finset.sum_const_zero]⟩
  have hφ : ∀ v, φ (TrivSqZeroExt.inr v) = ∑ k, v k • c k := fun v => by
    simp only [φ]
    rw [TrivSqZeroExt.liftEquivOfComm_apply, TrivSqZeroExt.lift_apply_inr,
      Fintype.linearCombination_apply]
  have hφe : ∀ k, φ (e k) = c k := fun k => by
    rw [hφ]
    simp [Pi.single_apply]
  have h := congrArg (spMap φ ≫ ·) hx
  simp only [MonObj.comp_mul] at h
  rw [hnat _ _ _ _ (fun i => hnil _), hnat _ _ _ _ (fun i => hnil _),
    hnat _ _ _ _ (fun i => by rw [hker _ (hd i)]; exact hnil _)] at h
  simp only [show ∀ k, φ (TrivSqZeroExt.inr (Pi.single k 1)) = c k from hφe] at h
  rw [h]
  congr 1
  funext i
  exact (congrArg φ (hker _ (hd i))).trans (hφ _)
end GlobalTheory.CharGerm
