-- Prove2me | solution 1 for GlobalTheory.ConstFam.exists_basis_of_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:01:59.599995+00:00
-- url     : https://prove2.me/submissions/1d71a9b0-9689-41bb-86f5-e19925efa248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSecIsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpandsAtSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsBasisOfIsExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution {L : Type} [Field L] {M : Type} [AddCommGroup M] [Module L M] {C : Type}
    [Finite C] {W : C → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module L (W x)] (p : ∀ x, M →ₗ[L] W x)
    (inj : ∀ m, (∀ x, p x m = 0) → m = 0) {Idx : C → Type} (bs : ∀ x, Module.Basis (Idx x) L (W x))
    (v : ∀ x, Idx x → M) (h₁ : ∀ x i, p x (v x i) = bs x i) (h₂ : ∀ x y i, y ≠ x → p y (v x i) = 0) :
    ∃ B : Module.Basis (Σ x, Idx x) L M, ∀ x i, B ⟨x, i⟩ = v x i := by
  classical
  have := Fintype.ofFinite C
  have key : ∀ x i, LinearMap.pi p (v x i) = Pi.basis bs ⟨x, i⟩ := fun x i => by
    rw [Pi.basis_apply]
    funext y
    by_cases h : y = x
    · subst h
      rw [LinearMap.pi_apply, h₁, Pi.single_eq_same]
    · rw [LinearMap.pi_apply, h₂ x y i h, Pi.single_eq_of_ne h]
  have hb : Function.Bijective (LinearMap.pi p) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun m hm => inj m fun x => congrFun hm x, ?_⟩
    rw [← LinearMap.range_eq_top, eq_top_iff, ← (Pi.basis bs).span_eq, Submodule.span_le]
    rintro _ ⟨⟨x, i⟩, rfl⟩
    exact ⟨v x i, key x i⟩
  refine ⟨(Pi.basis bs).map (LinearEquiv.ofBijective _ hb).symm, fun x i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.symm_apply_eq]
  exact (key x i).symm
end GlobalTheory.ConstFam
