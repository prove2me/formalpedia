-- Prove2me | solution 1 for GlobalTheory.ArcTransport.GtRel.isAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:43:59.231185+00:00
-- url     : https://prove2.me/submissions/4823b9ea-b456-4735-b1a6-e7ef799aff8d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_mul
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_injective
import Theorems.Thm_GlobalTheory_ArcTransport_pushF_cP
import Theorems.Thm_GlobalTheory_ArcTransport_thS_push
import Theorems.Thm_GlobalTheory_ArcTransport_gtRel_iff
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isAdd_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
include gp hT hc hw
namespace GlobalTheory.ArcTransport
namespace GtRel
theorem _root_.solution (hG : GlobalFnsSt) {u u' u'' : D.X → Fˣ} (hu : ∀ χ, u'' χ = u χ * u' χ) {g₀ g₀' g₀'' : GtPtF D F}
    {g g' g'' : GtPtF D' F} (h : GtRel w e u g₀ g) (h' : GtRel w e u' g₀' g') (h'' : GtRel w e u'' g₀'' g'')
    (H : g₀.IsAdd g₀' g₀'') : g.IsAdd g' g'' := by
  obtain ⟨b₁, v₁⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h
  obtain ⟨b₂, v₂⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h'
  obtain ⟨b₃, v₃⟩ := (gtRel_iff gp hT hc hw _ _ _).1 h''
  obtain ⟨b₀, v₀⟩ := (isAdd_iff _ _ _).1 H
  have hb : g''.b = g.b * g'.b := pushF_injective gp hT (by rw [pushF_mul, b₁, b₂, b₃, b₀])
  refine (isAdd_iff _ _ _).2 ⟨hb, fun χ y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Y := Sp F) y
  obtain ⟨χ, rfl⟩ := e.surjective χ
  have e₁ : vS (g₀''.s χ) y J * thS D y J (cP D _ χ) g₀.b g₀'.b = vS (g₀.s χ) y J * vS (g₀'.s χ) y J := v₀ χ y J hJ
  show vS (g''.s (e χ)) y J' * thS D' y J' (cP D' _ (e χ)) g.b g'.b = vS (g.s (e χ)) y J' * vS (g'.s (e χ)) y J'
  have c := thS_push gp hT hw hG hJ hJ' (cP D' _ (e χ)) g.b g'.b
  rw [pushF_cP gp hT hc, b₁, b₂, _root_.mul_assoc (cP D' _ (e χ)), ← hb] at c
  rw [c] at e₁
  have w₃ := v₃ χ y J J' hJ hJ'
  rw [hu, map_mul] at w₃
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have c₁ := congrArg Additive.ofMul (v₁ χ y J J' hJ hJ')
  have c₂ := congrArg Additive.ofMul (v₂ χ y J J' hJ hJ')
  have c₃ := congrArg Additive.ofMul w₃
  simp only [ofMul_mul, ofMul_inv] at a₁ c₁ c₂ c₃ ⊢
  linear_combination (norm := abel) a₁ - c₁ - c₂ + c₃
end GtRel
end GlobalTheory.ArcTransport
