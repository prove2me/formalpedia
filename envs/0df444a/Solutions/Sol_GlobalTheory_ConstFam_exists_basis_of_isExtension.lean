-- Prove2me | solution 1 for GlobalTheory.ConstFam.exists_basis_of_isExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:30.810695+00:00
-- url     : https://prove2.me/submissions/a301961b-9dca-4967-b98f-4a902aa67f85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Theorems.Thm_GlobalTheory_ConstFam_linearIndependent_of_isExtension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)
  (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)
namespace GlobalTheory.ConstFam
theorem _root_.solution {K L : Type} [Field K] [Field L] [Algebra K L] {V W : Type} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module L W] {g : V →ₛₗ[algebraMap K L] W} (hg : IsExtension g) {I : Type}
    (v : Module.Basis I K V) : ∃ B : Module.Basis I L W, ∀ i, B i = g (v i) := by
  refine ⟨Module.Basis.mk (linearIndependent_of_isExtension hg v.linearIndependent) ?_,
    fun i => Module.Basis.mk_apply _ _ i⟩
  rw [← hg.span, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Submodule.span K (Set.range v) := v.mem_span x
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul d y _ hy => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
end GlobalTheory.ConstFam
