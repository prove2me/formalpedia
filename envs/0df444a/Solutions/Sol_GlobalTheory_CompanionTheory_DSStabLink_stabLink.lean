-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.stabLink
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:34.576239+00:00
-- url     : https://prove2.me/submissions/26304060-b2f2-478a-8c30-250acce5b24d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_flow_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_deriv_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_inK_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_exp_mem_K
import Theorems.Thm_GlobalTheory_CompanionTheory_DSStabLink_exp_mem_UJ
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution : KExp → StabLink := by
  intro hK n ε H _ _ σ S E hσ hS U hU
  constructor
  · intro hst g hg v hv
    obtain ⟨X, hX, rfl⟩ := hK n ε g hg
    have := flow_mem (U.map S.subtype) (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)))
      ?_ ?_ ?_ ?_ v hv
    · simpa using this
    · intro v
      simp [hσ.1.1]
    · intro s t v
      have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
      simp only [Complex.ofReal_add, add_smul]
      rw [Matrix.exp_add_of_commute _ _ hc,
        hσ.1.2 _ (exp_mem_UJ ε hX.1 s) _ (exp_mem_UJ ε hX.1 t)]
      rfl
    · intro t v
      exact hσ.2.1 _ (exp_mem_UJ ε hX.1 t) v
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ?_, hS.real X hX.1 w⟩
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      by_cases h : ε a = ε b
      · exact Submodule.smul_mem _ _ ⟨_, hst a b h w hw, rfl⟩
      · simp [((inK_iff ε X).1 hX).1 a b h]
  · intro hst a b hab v hv
    have hL : ∀ X, inK ε X → ∑ c, ∑ d, X c d • (E c d v : H) ∈ U.map S.subtype := fun X hX =>
      deriv_mem _ _ _ (fun t => hst _ (exp_mem_K ε hX t) _ ⟨v, hv, rfl⟩) (hS.real X hX.1 v)
    have hs : ∀ (p q : Fin n) (z : ℂ),
        ∑ c, ∑ d, (Matrix.single p q z) c d • (E c d v : H) = z • (E p q v : H) := by
      intro p q z
      simp [Matrix.single_apply, ite_and]
    have hoff : ∀ (p q : Fin n) (z : ℂ), ε p = ε q → ∀ c d, ε c ≠ ε d →
        Matrix.single p q z c d = 0 := by
      intro p q z h c d hcd
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hcd h
    have hZ : ∀ z : ℂ, z • (E a b v : H) - star z • (E b a v : H) ∈ U.map S.subtype := by
      intro z
      have hin : inK ε (Matrix.single a b z - Matrix.single b a (star z)) := by
        rw [inK_iff]
        refine ⟨fun c d h => by simp [hoff a b z hab c d h, hoff b a _ hab.symm c d h], fun c d => ?_⟩
        simp only [Matrix.sub_apply, Matrix.single_apply, star_sub, apply_ite star, star_star,
          star_zero, neg_sub, and_comm]
      have := hL _ hin
      simpa only [Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, hs] using this
    have h1 := hZ 1
    have h2 := hZ Complex.I
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ (1 / 2 : ℂ) h1)
      (Submodule.smul_mem _ (-Complex.I / 2 : ℂ) h2)
    have e : (1 / 2 : ℂ) • ((1 : ℂ) • (E a b v : H) - star (1 : ℂ) • (E b a v : H)) +
        (-Complex.I / 2 : ℂ) • (Complex.I • (E a b v : H) - star Complex.I • (E b a v : H)) =
        (E a b v : H) := by
      simp only [star_one, Complex.star_def, Complex.conj_I]
      match_scalars
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
      · linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
    rw [e] at h3
    obtain ⟨y, hy, hye⟩ := h3
    have : y = E a b v := Subtype.ext hye
    exact this ▸ hy
end GlobalTheory.CompanionTheory.DSStabLink
