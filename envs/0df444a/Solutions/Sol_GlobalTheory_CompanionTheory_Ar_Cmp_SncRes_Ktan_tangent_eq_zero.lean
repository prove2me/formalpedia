-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.tangent_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:51:06.396647+00:00
-- url     : https://prove2.me/submissions/8c971374-ac9f-4035-8f6b-ee92e6a9ae98

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SndEqZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Ktan_aeval_dualPt
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Ktan_snd_eq_zero_of_span
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
open TrivSqZeroExt
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) [Fintype σ] (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω) (e : ℕ) (z : Fin e → S) (Z : Fin e → MvPolynomial σ ℚ) (N : Fin e → ℕ) (t v : σ → ℂ) (c : Fin e → ℂ), aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) → Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ → (∀ i, (z i : Ω) * aeval τ F ^ N i = aeval τ (Z i)) → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → eval t (map (algebraMap ℚ ℂ) F) ≠ 0 → (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) G)) = 0) → (∀ i, eval t (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t (map (algebraMap ℚ ℂ) F) ^ N i) → (∀ i, ∑ q, v q * eval t (pderiv q (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)) = 0) → v = 0 := by
  intro Ω _ _ σ _ τ F S e z Z N t v c hF0 hS hspan hz hker0 hFt hker1 hZc hZd
  have hψ : ∀ G : MvPolynomial σ ℚ, (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) =
      aeval (dualPt t v) (map (algebraMap ℚ ℂ) G) := fun G =>
    (aeval_map_algebraMap ℂ (dualPt t v) G).symm
  have hker : ∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → (aeval (dualPt t v) G : TrivSqZeroExt ℂ ℂ) = 0 := by
    intro G hG
    have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) G)
    rw [hψ]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [h1.1, hker0 G hG]; simp
    · rw [h1.2, hker1 G hG]; simp
  have memInv : (aeval τ F)⁻¹ ∈ S := hS ▸ Algebra.subset_adjoin (Set.mem_insert _ _)
  have memτ : ∀ q, τ q ∈ S := fun q => hS ▸ Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨q, rfl⟩)
  have hRS : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range ≤ S := by
    rw [← Algebra.adjoin_range_eq_range_aeval ℚ τ, hS]
    exact Algebra.adjoin_mono (Set.subset_insert _ _)
  have hsurjS : ∀ s ∈ S, ∃ r ∈ (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range, ∃ n : ℕ, s = r * (aeval τ F)⁻¹ ^ n := by
    rw [hS]
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with rfl | ⟨q, rfl⟩
      · exact ⟨1, Subalgebra.one_mem _, 1, by ring⟩
      · exact ⟨τ q, ⟨X q, aeval_X τ q⟩, 0, by ring⟩
    | algebraMap r => exact ⟨algebraMap ℚ Ω r, Subalgebra.algebraMap_mem _ r, 0, by ring⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      refine ⟨r * aeval τ F ^ n' + r' * aeval τ F ^ n, Subalgebra.add_mem _ (Subalgebra.mul_mem _ hr
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)) (Subalgebra.mul_mem _ hr'
        (Subalgebra.pow_mem _ (AlgHom.mem_range_self _ F) _)), n + n', ?_⟩
      rw [inv_pow, inv_pow, inv_pow]
      field_simp
      ring
    | mul y y' _ _ hy hy' =>
      obtain ⟨r, hr, n, rfl⟩ := hy
      obtain ⟨r', hr', n', rfl⟩ := hy'
      exact ⟨r * r', Subalgebra.mul_mem _ hr hr', n + n', by rw [pow_add]; ring⟩
  letI : Algebra (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range S := (Subalgebra.inclusion hRS).toRingHom.toAlgebra
  let xR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range := ⟨aeval τ F, AlgHom.mem_range_self _ F⟩
  have hxS : IsUnit (algebraMap _ S xR) :=
    isUnit_iff_exists_inv.2 ⟨⟨(aeval τ F)⁻¹, memInv⟩, Subtype.ext (by
      show aeval τ F * (aeval τ F)⁻¹ = 1
      exact mul_inv_cancel₀ hF0)⟩
  haveI : IsLocalization.Away xR S := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      rw [map_pow]
      exact hxS.pow n
    · intro s
      obtain ⟨r, hr, n, hs⟩ := hsurjS s s.2
      refine ⟨(⟨r, hr⟩, ⟨xR ^ n, n, rfl⟩), Subtype.ext ?_⟩
      show (s : Ω) * ((xR ^ n : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = r
      rw [SubmonoidClass.coe_pow, hs]
      show r * (aeval τ F)⁻¹ ^ n * aeval τ F ^ n = r
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hF0, one_pow, mul_one]
    · intro a b h
      have h' : ((algebraMap _ S a : S) : Ω) = ((algebraMap _ S b : S) : Ω) := congrArg (fun s : S => (s : Ω)) h
      exact ⟨1, congrArg _ (Subtype.ext h')⟩
  have hsurjR : Function.Surjective ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict :
      MvPolynomial σ ℚ →+* (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) := by
    rintro ⟨y, G, rfl⟩
    exact ⟨G, rfl⟩
  let ψR : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range →+* TrivSqZeroExt ℂ ℂ :=
    RingHom.liftOfSurjective _ hsurjR ⟨(aeval (dualPt t v) : MvPolynomial σ ℚ →ₐ[ℚ] TrivSqZeroExt ℂ ℂ).toRingHom,
      fun G hG => by
        rw [RingHom.mem_ker] at hG ⊢
        exact hker G (congrArg Subtype.val hG)⟩
  have hψR : ∀ G : MvPolynomial σ ℚ, ψR ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G) =
      aeval (dualPt t v) G := fun G => RingHom.liftOfSurjective_comp_apply _ hsurjR _ G
  have hxR : xR = (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict F := rfl
  have hFt' : IsUnit (aeval (dualPt t v) F : TrivSqZeroExt ℂ ℂ) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ, (aeval_dualPt t v _).1]
    exact isUnit_iff_ne_zero.2 hFt
  have hu : IsUnit (ψR xR) := by rw [hxR, hψR]; exact hFt'
  let φS : S →+* TrivSqZeroExt ℂ ℂ := IsLocalization.Away.lift xR hu
  have hφS : ∀ G : MvPolynomial σ ℚ, φS (algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict G)) =
      aeval (dualPt t v) G := fun G => by
    rw [IsLocalization.Away.lift_eq, hψR]
  have hZ : ∀ i, (aeval (dualPt t v) (Z i) : TrivSqZeroExt ℂ ℂ) =
      inl (c i) * aeval (dualPt t v) F ^ N i := by
    intro i
    have h0 : (aeval (dualPt t v) (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i) :
        TrivSqZeroExt ℂ ℂ) = 0 := by
      have h1 := aeval_dualPt t v (map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i)
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [h1.1]; simp [hZc i]
      · rw [h1.2, hZd i]; simp
    rw [map_sub, map_mul, map_pow, aeval_C, algebraMap_eq_inl, ← hψ, ← hψ, sub_eq_zero] at h0
    exact h0
  have hφz : ∀ i, snd (φS.toRatAlgHom (z i)) = 0 := by
    intro i
    have e1 : z i * algebraMap _ S (xR ^ N i) =
        algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (Z i)) := Subtype.ext (by
      show (z i : Ω) * ((xR ^ N i : (aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).range) : Ω) = aeval τ (Z i)
      rw [SubmonoidClass.coe_pow]
      exact hz i)
    have e2 := congrArg φS e1
    have hφx : φS (algebraMap _ S xR) = aeval (dualPt t v) F := by rw [hxR]; exact hφS F
    rw [map_mul, map_pow, map_pow, hφx, hφS, hZ] at e2
    have e3 : φS (z i) = inl (c i) := (hFt'.pow (N i)).mul_left_inj.1 e2
    show snd (φS (z i)) = 0
    rw [e3, snd_inl]
  funext q
  have h := snd_eq_zero_of_span φS.toRatAlgHom z hspan hφz ⟨τ q, memτ q⟩
  have hq : (⟨τ q, memτ q⟩ : S) = algebraMap _ S ((aeval τ : MvPolynomial σ ℚ →ₐ[ℚ] Ω).rangeRestrict (X q)) :=
    Subtype.ext (aeval_X τ q).symm
  change snd (φS ⟨τ q, memτ q⟩) = 0 at h
  rw [hq, hφS, aeval_X] at h
  simpa [dualPt] using h
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan
