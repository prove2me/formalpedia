-- Prove2me | solution 1 for GlobalTheory.NL.Model.ex_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:44.341153+00:00
-- url     : https://prove2.me/submissions/5fe689f1-2d32-4894-9d6f-ef89266a5441

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
section
noncomputable section
namespace GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
section Series
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
end Series
section Generic
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
end Generic
section Concrete
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem periodTensor_ιV_injective (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) :
    Function.Injective (_root_.Formalism.WeaklyAdmissibleFiltrations.ιV PD : T.V ⊗[Qp] B →ₗ[LL] T.V ⊗[Qp] BdR) := by
  have hf : Function.Injective ((PD.ι.toLinearMap).restrictScalars Qp) := PD.ι_inj
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := T.V) _ hf
open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} in
private theorem levB_smul_eq_powerSeriesSmul_lemma_2 {Zl Ai : Type} [CommRing Zl] [CommRing Ai]
    [Algebra Zl O] [Algebra Zl Ai] {W : _root_.Formalism.BasicNotions.LocWach PD LL O v n} {RW : Type} [CommRing RW]
    [Algebra O RW] {inclR : TensorProduct Zl O Ai →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → RW →ₐ[O] RW} {πA : TensorProduct Zl O Ai}
    {E : _root_.Formalism.BasicNotions.EtTie W (TensorProduct Zl O Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai}
    {tS zS : BdR} (S : _root_.Formalism.BasicNotions.CmpTie W E ιdR p1 tS zS) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (i : ZMod n) (ζ : LL)
    (a : _root_.Formalism.BasicNotions.LetA O n) (x : ↥(W.N T)) :
    S.levB T i ζ (a • x) = _root_.GlobalTheory.NL.conv (W.lev i ζ a) (S.levB T i ζ x) := by
  funext k
  refine periodTensor_ιV_injective (PD := PD) T ?_
  obtain ⟨m, hm⟩ := S.levB_supp T i ζ x
  rw [← S.levN_eq, W.levN_smul, _root_.GlobalTheory.NL.conv,
    map_finsum _ (_root_.GlobalTheory.NL.Model.conv_finite _ hm k)]
  simp only [map_smul, S.levN_eq]
end Concrete
end GlobalTheory.NL.Model
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
open TensorProduct
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1) (a : _root_.GlobalTheory.NL.AA K LL)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ (a • x) =
      _root_.GlobalTheory.NL.conv ((H.W K s LL h).lev i ζ a) (_root_.GlobalTheory.NL.ex C h T i ζ x) :=
  levB_smul_eq_powerSeriesSmul_lemma_2 _ T i ζ a x
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model
