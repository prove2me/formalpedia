-- Prove2me | solution 1 for GlobalTheory.NL.Model.wachExpansion_smul_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:07:05.13688+00:00
-- url     : https://prove2.me/submissions/4106da2d-cfe2-47b0-935d-e30cfbffed22

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_conv_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
namespace GlobalTheory.NL.Model
theorem _root_.solution (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (e : ↥(W.N T) → ℤ → T.V ⊗[Qp] B) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (he : ∀ x k, W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (e x k))
    (a : LetA O n) (x : ↥(W.N T)) : e (a • x) = conv (W.lev i ζ a) (e x) := by
  have hinj : Function.Injective (ιV PD (LL := LL) (V := T.V)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := T.V)
      (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj
  obtain ⟨m, hm⟩ := hs x
  funext k
  apply hinj
  rw [← he, W.levN_smul]
  unfold conv
  rw [map_finsum _ (conv_finite (W.lev i ζ a) hm k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.map_smul, he]
end GlobalTheory.NL.Model
