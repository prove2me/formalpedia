-- Prove2me | solution 1 for GlobalTheory.HolHomOnto.exists_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:27:29.462321+00:00
-- url     : https://prove2.me/submissions/20a10d7f-d50f-4609-acf8-0e4a15cf5d55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsDerivAtOfSurjective
import Theorems.Thm_GlobalTheory_HolChart_derivation_eq_zero
import Theorems.Thm_GlobalTheory_HolChart_exists_etale_coords_vanishing
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_fst_valR
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_iff
import Theorems.Thm_GlobalTheory_TangentOrigin_eq_spMap_of_evalPt
import Theorems.Thm_GlobalTheory_TangentOrigin_exists_evalPt_eq
import Theorems.Thm_GlobalTheory_TangentOrigin_ext_evalPt
import Theorems.Thm_GlobalTheory_exists_holomorphic_section_of_etale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HolHomOnto
open GlobalTheory.TangentOrigin GlobalTheory.HolHom
namespace GlobalTheory.HolHomOnto
theorem _root_.solution {Y : Scheme.{0}} (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)),
      ⊤ ≤ x ⁻¹ᵁ U ∧ IsOpen W ∧ 0 ∈ W ∧
      (∀ w ∈ W, ∃ p : Sp ℂ ⟶ Y, p ≫ s = 𝟙 _ ∧ ⊤ ≤ p ⁻¹ᵁ U ∧ ∀ i, valAt' p U (t i) = w i) ∧
      ∀ v v' : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
        v' ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap fstC ≫ v = x → spMap fstC ≫ v' = x →
        (∀ i, (valR v U (t i)).snd = (valR v' U (t i)).snd) → v = v' := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (x (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  let c : ℂ →+* Γ(Y, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn s U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hconst : ∀ {R : Type} [CommRing R] (ψ : ℂ →+* R) (y : Sp R ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = spMap ψ →
      ∀ a, evalPt y U hy (c a) = ψ a := by
    intro R _ ψ y hy hys a
    rw [← hcc, evalPt_constFn]
    exact (congrArg (fun y : Sp R ⟶ Sp ℂ => evalPt y ⊤ le_rfl
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) hys).trans (evalPt_spMap _ a)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := (le_preimage_iff x U).2 hp
  have hxc : ∀ a, evalPt x U hxU (c a) = a := hconst (RingHom.id ℂ) x hxU (hx.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) hxc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(Y, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U) := hφ
  let eA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt x U hxU with commutes' := hxc }
  obtain ⟨W, σ, m, f, ε, hW, hW0, -, -, -, hσt, -⟩ :=
    exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0
  refine ⟨n, U, fun i => φ (MvPolynomial.X i), W, hxU, hW, hW0, fun w hw => ?_, fun v v' hv hv' h0 h0' ht => ?_⟩
  · obtain ⟨p, hpU, hpσ⟩ := exists_evalPt_eq hU (σ w).toRingHom
    refine ⟨p, ?_, hpU, fun i => ?_⟩
    · refine (eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)
      rw [← evalPt_constFn s p U hpU, hpσ, hcc]
      exact (σ w).commutes a
    · rw [valAt'_eq_evalPt _ _ hpU, hpσ]
      exact hσt w hw i
  · have hvU := (le_preimage_dual_iff h0 U).2 hxU
    have hvU' := (le_preimage_dual_iff h0' U).2 hxU
    have e1 : ∀ f, valR v U f = evalPt v U hvU f := valR_eq _ _ hvU
    have e2 : ∀ f, valR v' U f = evalPt v' U hvU' f := valR_eq _ _ hvU'
    have f1 : ∀ f, (evalPt v U hvU f).fst = evalPt x U hxU f := fun f => by
      rw [← e1, fst_valR h0 hxU, valAt'_eq_evalPt]
    have f2 : ∀ f, (evalPt v' U hvU' f).fst = evalPt x U hxU f := fun f => by
      rw [← e2, fst_valR h0' hxU, valAt'_eq_evalPt]
    let D : Γ(Y, U) →+ ℂ :=
      { toFun := fun f => (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd
        map_zero' := by simp
        map_add' := fun f f' => by
          simp only [map_add, TrivSqZeroExt.snd_add]
          ring }
    have hD : ∀ f, D f = (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd := fun _ => rfl
    have hz : D = 0 := by
      refine HolChart.derivation_eq_zero φ hφ (evalPt x U hxU) D (fun a => ?_) (fun f f' => ?_) fun i => ?_
      · rw [hD, hφc', hconst _ v hvU hv, hconst _ v' hvU' hv', sub_self]
      · rw [hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, f1, f1, f2, f2]
        ring
      · rw [hD, ← e1, ← e2, ht, sub_self]
    refine ext_evalPt hU hvU hvU' (RingHom.ext fun f => TrivSqZeroExt.ext ((f1 f).trans (f2 f).symm) ?_)
    have := hD f
    rw [hz] at this
    exact sub_eq_zero.1 this.symm
end GlobalTheory.HolHomOnto
