-- Prove2me | solution 1 for GlobalTheory.LocalQuad.Approx.abv_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:07.079694+00:00
-- url     : https://prove2.me/submissions/f1c1bb24-6254-49ff-b424-1db11c597734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
private theorem not_isEquiv_adicAbv_real_place (v : HeightOneSpectrum (𝓞 F)) (σ : F →+* ℝ) :
    ¬(NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv
      (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1 := by
  intro hE
  have h2 := (hE.le_one_iff (x := (2 : F))).1
    (by simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v 2)
  change InfinitePlace.mk (Complex.ofRealHom.comp σ) 2 ≤ 1 at h2
  rw [InfinitePlace.apply] at h2
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  simp only [RingHom.comp_apply, hσ2] at h2
  norm_num at h2
end GlobalTheory.LocalQuad.Approx
end

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
variable {F : Type} [Field F] [NumberField F]
open NumberField IsDedekindDomain
open scoped Matrix WithZero
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.LocalQuad.Approx
namespace _root_.GlobalTheory.LocalQuad.Approx
theorem _root_.solution (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise fun i j ↦ ¬(_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsEquiv
      (_root_.GlobalTheory.LocalQuad.Approx.abv T j) := by
  rintro (v | σ) (w | τ) hne hE
  · have hvw : v.1 ≠ w.1 := fun h ↦ hne (congrArg Sum.inl (Subtype.ext h))
    have hle : ¬v.1.asIdeal ≤ w.1.asIdeal := fun hle ↦
      hvw (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le w.1.isPrime.ne_top hle))
    obtain ⟨r, hrv, hrw⟩ := Set.not_subset.1 hle
    have h1 := hE.lt_one_iff (x := algebraMap (𝓞 F) F r)
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ < 1 ↔
      NumberField.HeightOneSpectrum.adicAbv F w.1 _ < 1 at h1
    rw [← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding,
      FinitePlace.norm_lt_one_iff_mem, FinitePlace.norm_lt_one_iff_mem] at h1
    exact hrw (h1.1 hrv)
  · exact not_isEquiv_adicAbv_real_place v.1 τ hE
  · exact not_isEquiv_adicAbv_real_place w.1 σ hE.symm
  · have hmk := (InfinitePlace.eq_iff_isEquiv (w := InfinitePlace.mk (Complex.ofRealHom.comp σ))
      (v := InfinitePlace.mk (Complex.ofRealHom.comp τ))).2 hE
    rw [InfinitePlace.mk_eq_iff] at hmk
    have key : Complex.ofRealHom.comp σ = Complex.ofRealHom.comp τ := by
      rcases hmk with h | h
      · exact h
      · rw [← h]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
    apply hne
    congr 1
    ext x
    simpa using congrArg (fun φ : F →+* ℂ ↦ φ x) key
end _root_.GlobalTheory.LocalQuad.Approx
end GlobalTheory.LocalQuad.Approx
