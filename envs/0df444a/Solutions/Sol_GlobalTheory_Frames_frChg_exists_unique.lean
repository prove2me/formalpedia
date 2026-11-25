-- Prove2me | solution 1 for GlobalTheory.Frames.frChg_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:42:30.725994+00:00
-- url     : https://prove2.me/submissions/f1261ad1-7bb9-4e75-b30d-6f75b233bb5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FrameChangeExistsUniqueOfSamePoint
import Theorems.Thm_P2M_GlobalTheory_Frames_ChgOf_gen_unit__6413ca301ad1
import Theorems.Thm_GlobalTheory_Frames_ChgOf_secBC_id_iff
import Theorems.Thm_GlobalTheory_T_exists_tangent_module_universal_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory.Frames.ChgOf
namespace GlobalTheory.Frames
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S), (y'.x = y.x → ∃ (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ), (∀ τ, IsUnit (g τ).det) ∧ FrChg g (a : S) y y') ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y y' → g = g' ∧ a = a' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y'
  obtain ⟨x', hover', u', tan', eig', basis', s', gen'⟩ := y'
  constructor
  · intro hx
    simp only at hx
    subst hx
    obtain ⟨N, _, _, v, ρ, hv, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo S y.x
    choose g hg using fun τ i => (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).exists
    choose h hh using fun τ i => (basis' τ (y.u τ i) (y.tan τ i) (y.eig τ i)).exists
    obtain ⟨a, ha⟩ := gen_unit' y.s s' y.gen gen'
    refine ⟨fun τ => Matrix.of (g τ), a, fun τ => ?_, rfl, fun τ i => hg τ i, (secBC_id_iff _ _ _ _).2 ha⟩
    choose b hb using fun i => (htan _).1 (y.tan τ i)
    choose b' hb' using fun i => (htan _).1 (tan' τ i)
    have eb : y.u τ = fun i => v (b i) := funext fun i => (hb i).symm
    have eb' : u' τ = fun i => v (b' i) := funext fun i => (hb' i).symm
    have h1 : ∀ i, b' i = ∑ j, g τ i j • b j := fun i => by
      have := hg τ i
      rw [eb, hcomb, ← hb' i] at this
      exact hv this
    have h2 : ∀ i, b i = ∑ j, h τ i j • b' j := fun i => by
      have := hh τ i
      rw [eb', hcomb, ← hb i] at this
      exact hv this
    have hm : Matrix.of (h τ) * Matrix.of (g τ) = 1 := by
      funext i
      refine (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique ?_ ?_
      · rw [← hb i, eb, hcomb]
        congr 1
        rw [h2 i]
        simp only [h1, Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
        exact Finset.sum_comm
      · rw [← hb i, eb, hcomb]
        congr 1
        simp [Matrix.one_apply]
    exact Matrix.isUnit_det_of_left_inverse hm
  · rintro g g' a a' ⟨hx, h1, h2⟩ ⟨-, h1', h2'⟩
    simp only at hx h1 h2 h1' h2'
    subst hx
    refine ⟨funext fun τ => funext fun i => ?_, ?_⟩
    · exact (y.basis τ (u' τ i) (tan' τ i) (eig' τ i)).unique (h1 τ i) (h1' τ i)
    · exact (y.gen s').unique ((secBC_id_iff _ _ _ _).1 h2) ((secBC_id_iff _ _ _ _).1 h2')
end GlobalTheory.Frames
