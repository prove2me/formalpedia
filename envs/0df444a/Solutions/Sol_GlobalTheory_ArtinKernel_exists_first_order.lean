-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.exists_first_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:09.050189+00:00
-- url     : https://prove2.me/submissions/7bd2bdfa-03a6-4c2f-9d20-1a0af1152063

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnFamPtAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfLogDeriv
import Theorems.Thm_GlobalTheory_ArtinKernel_exists_derivation
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_congr
import Theorems.Thm_GlobalTheory_ArtinKernel_evalPt_const
import Theorems.Thm_GlobalTheory_ArtinKernel_resPt_left
import Theorems.Thm_GlobalTheory_ArtinKernel_residue_evalPt
import Theorems.Thm_GlobalTheory_ArtinKernel_subsingleton_primeSpectrum
import Theorems.Thm_GlobalTheory_ArtinKernel_top_le_const
import Theorems.Thm_GlobalTheory_ArtinKernel_top_le_iff_residue
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_evalPt_res
import Theorems.Thm_GlobalTheory_TangentOrigin_ex_zero
import Theorems.Thm_GlobalTheory_TangentOrigin_ex_zero_left
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_fderiv_val_res
import Theorems.Thm_GlobalTheory_TangentOrigin_isDiff_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_jet_snd
import Theorems.Thm_GlobalTheory_TangentOrigin_tangent_bijection
import Theorems.Thm_GlobalTheory_TangentOrigin_top_le_preimage_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.ArtinKernel
open GlobalTheory.TangentOrigin
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.ArtinKernel
theorem _root_.solution (ρ : R →ₐ[ℂ] ℂ) (hρ : ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R)
    {U : A.left.Opens} {t : Fin g → Γ(A.left, U)} (hU : IsAffineOpen U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U)
    (huniq : ∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) →
      (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) →
      (∀ i, D (t i) = 0) → D = 0)
    (ht : HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (x : spO R ⟶ A) (hx : resPt ρ ≫ x = u.ex 0) (hx1 : x ≠ 1) :
    ∃ (κ : R →ₗ[ℂ] ℂ) (w : Fin g → ℂ), κ 1 = 0 ∧ w ≠ 0 ∧
      ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
        (∀ r, κ (r * evalPt (R := R) x.left W h f) =
          ρ r * κ (evalPt (R := R) x.left W h f) + ρ (evalPt (R := R) x.left W h f) * κ r) ∧
        κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by
  classical
  have hsub := subsingleton_primeSpectrum (R := R)
  have hy : spMap ρ.toRingHom ≫ x.left = (u.ex 0).left := by
    rw [← resPt_left, ← Over.comp_left, hx]
  have hmem : ∀ W : A.left.Opens, ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W → ⊤ ≤ x.left ⁻¹ᵁ W := fun W hW =>
    (top_le_iff_residue ρ.toRingHom x.left _ hy W).2 hW
  have hres : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
      ρ (evalPt (R := R) x.left W h f) = valAt' (u.ex 0).left W f := fun W h f =>
    residue_evalPt ρ.toRingHom x.left _ hy W h f
  let J := {q : Σ W : A.left.Opens, Γ(A.left, W) // ⊤ ≤ x.left ⁻¹ᵁ q.1}
  let s : J → R := fun q => evalPt (R := R) x.left q.1.1 q.2 q.1.2
  have hxU := hmem U h0
  have hs : ∃ q : J, s q ≠ algebraMap ℂ R (ρ (s q)) := by
    by_contra hcon
    push Not at hcon
    apply hx1
    have e : evalPt (R := R) x.left U hxU =
        evalPt (R := R) (toUnit (spO R) ≫ u.ex 0).left U (top_le_const (R := R) (u.ex 0) U h0) := by
      ext f
      rw [evalPt_const (u.ex 0) U _ h0, ← hres U hxU f]
      exact hcon ⟨⟨U, f⟩, hxU⟩
    have e2 := ext_evalPt hU hxU _ e
    apply Over.OverMorphism.ext
    rw [e2, ex_zero u, MonObj.comp_one]
  obtain ⟨κ, hκ1, hκne, hκ⟩ := exists_derivation ρ hρ s hs
  let w : Fin g → ℂ := fun i => κ (evalPt (R := R) x.left U hxU (t i))
  have core : ∀ (W : A.left.Opens) (h : ⊤ ≤ x.left ⁻¹ᵁ W) (f : Γ(A.left, W)),
      κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := by
    intro W h f
    have hW0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := (top_le_iff_residue ρ.toRingHom x.left _ hy W).1 h
    obtain ⟨V, hVaff, hV0, hVle⟩ : ∃ V : A.left.Opens, IsAffineOpen V ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V ∧
        V ≤ W ⊓ U := by
      have hpt : (u.ex 0).left (default : PrimeSpectrum ℂ) ∈ W ⊓ U := ⟨hW0 trivial, h0 trivial⟩
      obtain ⟨V, hV, hpV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens A.left)) hpt
      refine ⟨V, hV, fun q _ => ?_, hVle⟩
      have hq : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      rw [hq]
      exact hpV
    have hVW : V ≤ W := hVle.trans inf_le_left
    have hVU : V ≤ U := hVle.trans inf_le_right
    have hxV := hmem V hV0
    let ψ := evalPt (R := R) x.left V hxV
    have hL : ∀ f r, κ (r * ψ f) = ρ r * κ (ψ f) + ρ (ψ f) * κ r := fun f r => hκ ⟨⟨V, f⟩, hxV⟩ r
    obtain ⟨v0, hv0, hv0e⟩ := exists_evalPt_eq hVaff (jetOf ρ κ hκ1 ψ hL)
    have hc : ∀ a : ℂ, ψ (constFn A.hom V a) = algebraMap ℂ R a := by
      intro a
      have hxw : x.left ≫ A.hom = spMap (algebraMap ℂ R) := Over.w x
      show evalPt (R := R) x.left V hxV (constFn A.hom V a) = _
      rw [evalPt_constFn A.hom x.left V hxV a, evalPt_congr hxw ⊤ le_rfl le_rfl, evalPt_spMap]
    have hv0w : v0 ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
      apply eq_spMap_of_evalPt
      intro a
      rw [← evalPt_constFn A.hom v0 V hv0 a, hv0e]
      refine TrivSqZeroExt.ext ?_ ?_
      · change ρ (ψ (constFn A.hom V a)) = _
        rw [hc, AlgHom.commutes]
        rfl
      · change κ (ψ (constFn A.hom V a)) = _
        rw [hc, Algebra.algebraMap_eq_smul_one, map_smul, hκ1, smul_zero]
        rfl
    let v : epsR ℂ ⟶ A := Over.homMk v0 hv0w
    have hvt : IsTangent v := by
      show spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v0 = η[A].left
      rw [← ex_zero_left u]
      have hh : ⊤ ≤ (spMap fstC ≫ v0) ⁻¹ᵁ V := (top_le_preimage_iff v0 V).1 hv0
      apply ext_evalPt hVaff hh hV0
      ext f
      rw [evalPt_spMap_comp fstC v0 V hv0 hh, hv0e, ← valAt'_eq_evalPt _ _ hV0, ← hres V hxV f]
      rfl
    obtain ⟨wV, hwV, -⟩ := (tangent_bijection A L g u ⟨U, t, hU, h0, huniq, ht⟩).1 v hvt
    have hv0V : ⊤ ≤ v.left ⁻¹ᵁ V := hv0
    have hjet := (isDiff_iff hvt hVaff hv0V hV0 wV).1 hwV
    have hV : ∀ f' : Γ(A.left, V), κ (ψ f') = fderiv ℂ (fun z => valAt' (u.ex z).left V f') 0 wV := by
      intro f'
      have e1 : (evalPt v0 V hv0 f').snd = κ (ψ f') := by
        rw [hv0e]
        rfl
      rw [← e1, show evalPt v0 V hv0 = evalPt v.left V hv0V from rfl, hjet, jet_snd]
    have hw : wV = w := by
      funext i
      have e2 := hV (resG A.left hVU (t i))
      have e3 : ψ (resG A.left hVU (t i)) = evalPt (R := R) x.left U hxU (t i) :=
        evalPt_res x.left hVU hxU hxV (t i)
      rw [e3, fderiv_val_res u hVU h0 hV0 (t i)] at e2
      have hd : HasFDerivAt (fun z => valAt' (u.ex z).left U (t i))
          ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.id ℂ (Fin g → ℂ))) 0 :=
        hasFDerivAt_pi'.1 ht i
      rw [hd.fderiv] at e2
      simpa using e2.symm
    show κ (evalPt (R := R) x.left W h f) = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w
    rw [← evalPt_res x.left hVW h hxV f, ← fderiv_val_res u hVW hW0 hV0 f, ← hw]
    exact hV _
  refine ⟨κ, w, hκ1, ?_, fun W h f => ⟨fun r => hκ ⟨⟨W, f⟩, h⟩ r, core W h f⟩⟩
  intro hw0
  obtain ⟨q, hq⟩ := hκne
  apply hq
  have h5 := core q.1.1 q.2 q.1.2
  rw [hw0, ContinuousLinearMap.map_zero] at h5
  exact h5
end GlobalTheory.ArtinKernel
