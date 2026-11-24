-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.integral_char_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:37.002904+00:00
-- url     : https://prove2.me/submissions/fe5d1a87-a2a9-4cd4-9fb8-2ac537e0404d

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_mem_latR_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_sum_places_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (N : ℕ)
    [Countable (latR ρ N)]
    (D : Set (InfinitePlace F → ℝ)) (hD : IsAddFundamentalDomain (latR ρ N) D volume)
    (β : F) (hβ : β ≠ 0) (hint : ∃ r : 𝓞 F, (r : F) = (N : F) * β) :
    ∫ x in D, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) = 0 := by
  classical
  set f : (InfinitePlace F → ℝ) → ℂ := fun x =>
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((∑ w, ρ w β * x w : ℝ) : ℂ)) with hf
  have hadd : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.ofReal_add, Complex.exp_add]
  have hper : ∀ (g : latR ρ N) x, f (g +ᵥ x) = f x := by
    rintro ⟨g, hg⟩ x
    obtain ⟨s, rfl⟩ := (mem_latR_iff ρ N g).1 hg
    obtain ⟨r, hr⟩ := hint
    obtain ⟨z, hz⟩ := sum_places_int hF ρ hρ (r * s)
    have hrs : ((r * s : 𝓞 F) : F) = (N : F) * β * (s : F) := by
      rw [← hr]
      first
        | rfl
        | simp
    have h1 : f (fun w => ρ w ((N : F) * (s : F))) = 1 := by
      have : (∑ w, ρ w β * ρ w ((N : F) * (s : F))) = (z : ℝ) := by
        rw [← hz]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← map_mul]
        congr 1
        rw [hrs]
        ring
      simp only [hf, this]
      have := Complex.exp_int_mul_two_pi_mul_I z
      rw [← this]
      congr 1
      push_cast
      ring
    show f ((fun w => ρ w ((N : F) * (s : F))) + x) = f x
    rw [hadd, h1, one_mul]
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hρ0 : ρ w0 β ≠ 0 := by
    simpa using hβ
  let x0 : InfinitePlace F → ℝ := Pi.single w0 (1 / (2 * ρ w0 β))
  have hx0 : f x0 = -1 := by
    have : (∑ w, ρ w β * x0 w) = 1 / 2 := by
      rw [Finset.sum_eq_single w0]
      · simp only [x0, Pi.single_eq_same]
        field_simp
      · intro b _ hb
        simp [x0, Pi.single_eq_of_ne hb]
      · simp
    simp only [hf, this]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have hD' : IsAddFundamentalDomain (latR ρ N) (x0 +ᵥ D) volume := hD.vadd_of_comm x0
  have heq : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f x := hD'.setIntegral_eq hD hper
  have htr : ∫ x in x0 +ᵥ D, f x = ∫ x in D, f (x0 + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℝ)) x0).setIntegral_image_emb
      (measurableEmbedding_addLeft x0) f D
    rw [← this, ← Set.image_vadd]
    rfl
  have hmul : ∫ x in D, f (x0 + x) = - ∫ x in D, f x := by
    simp only [hadd, hx0]
    rw [integral_const_mul]
    ring
  have h2 : ∫ x in D, f x = - ∫ x in D, f x := by
    rw [← hmul, ← htr, heq]
  have h3 : (2 : ℂ) * ∫ x in D, f x = 0 := by
    linear_combination h2
  simpa using h3
end GlobalTheory.CompanionTheory.SW.FD
