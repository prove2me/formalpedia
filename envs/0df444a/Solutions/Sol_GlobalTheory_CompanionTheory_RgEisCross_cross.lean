-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisCross.cross
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:58.40653+00:00
-- url     : https://prove2.me/submissions/f784f874-2398-4f6b-81da-b162943488c5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicSeriesUniformTubeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SectionInvarianceCosetSumStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetSeriesSummableShiftedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoarseLipschitzExponentialEstimateStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossingOfWallsAndHeights
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisCross_sec_inv
import Theorems.Thm_GlobalTheory_T_coarse_lipschitz_exponential_estimate
import Theorems.Thm_GlobalTheory_T_coset_series_summable_shifted
import Theorems.Thm_GlobalTheory_T_holomorphic_series_uniform_tube
import Theorems.Thm_GlobalTheory_T_section_invariance_coset_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisCross
namespace GlobalTheory.CompanionTheory.RgEisCross
theorem _root_.solution (hSec : SecLaw) (hHt : HtLip) (hSt : PiLocalization₂) (hWL : WallLaw) : Cross := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ Q P P' c η η' β ξ L R D Op H Ω hPQ hP'Q hP hP' hη hη' hβ hξ hW hΩ hx
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have parRes : ∀ (P : Subgroup G), IsPar Γ K P c → IsPar (Γ ⊓ Q) K P c := fun _ h =>
    ⟨h.closed, h.iwa, ⟨h.ch.mul, h.ch.norm, fun γ hγ hp => h.ch.rat γ hγ.1 hp, h.ch.cont⟩⟩
  have htRes : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → IsHt (Γ ⊓ Q) K P f := fun _ _ h =>
    ⟨h.left, h.right, fun γ hγ hp => h.rat γ hγ.1 hp, h.cont⟩
  obtain ⟨-, -, hbound⟩ := hWL G W K ρ hK hρ (Γ ⊓ Q) P P' c η η' β L R D Op H (parRes P hP) (parRes P' hP')
    (htRes P η hη) (htRes P' η' hη') (htRes P' β hβ) hW
  have hξinv : ∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x := by
    intro γ h1 h2 x
    rw [hξ.left γ h2, hξ.rat γ h1 h2, zero_add]
  have htinv : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro P f hf γ h1 h2 x
    rw [hf.left γ h2, hf.rat γ h1 h2, zero_add]
  have iwaQ : Iwa Q K := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hP.iwa g
    exact ⟨p, hPQ hp, k, hk, e⟩
  have mξ := hHt G Γ K Q ξ hK iwaQ hξ
  have mη := hHt G Γ K P η hK hP.iwa hη
  have mη' := hHt G Γ K P' η' hK hP'.iwa hη'
  have mβ := hHt G Γ K P' β hK hP'.iwa hβ
  let t : Cos (Γ ⊓ Q) Γ → ℂ × ℂ → G → (L →L[ℂ] W) := fun r l g =>
    Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
  have hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g := by
    intro r g p v
    have h1 : Differentiable ℂ fun τ : ℂ => H (p + τ • v).1 (rep r * g) :=
      (hW.hol (rep r * g)).comp (by fun_prop)
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).2 * ξ (rep r * g)) := by fun_prop
    exact h2.smul h1
  have hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × G => t r y.1 y.2 := by
    intro r
    have h0 : Continuous fun y : (ℂ × ℂ) × G => rep r * y.2 := by fun_prop
    have h1 : Continuous fun y : (ℂ × ℂ) × G => H y.1.1 (rep r * y.2) :=
      hW.cont.comp (continuous_fst.fst.prodMk h0)
    have h2 : Continuous fun y : (ℂ × ℂ) × G => ξ (rep r * y.2) := hξ.cont.comp h0
    have h3 : Continuous fun y : (ℂ × ℂ) × G => Complex.exp (y.1.2 * ξ (rep r * y.2)) :=
      Complex.continuous_exp.comp ((continuous_fst.snd).mul (Complex.continuous_ofReal.comp h2))
    exact h3.smul h1
  have hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : Cos (Γ ⊓ Q) Γ → ℝ, Summable u ∧
      ∀ l ∈ tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r := by
    intro x hxΩ g
    obtain ⟨a, b, ε, hε, hRa, hbR, hbx, hxa, hconv⟩ := hx x hxΩ
    obtain ⟨M, hM⟩ := hbound a b hRa hbR
    have inv₁ : ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => a * η x) (γ * x) = (fun x => a * η x) x := by
      intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    have inv₂ : ∀ γ ∈ Γ, γ ∈ P' → ∀ x, (fun x => β x - b * η' x) (γ * x) = (fun x => β x - b * η' x) x := by
      intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    have m₁ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |a * η (g * u) - a * η g| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη C hC
      refine ⟨|a| * A, fun g u hu => ?_⟩
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg a)
    have m₂ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C,
        |(β (g * u) - b * η' (g * u)) - (β g - b * η' g)| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη' C hC
      obtain ⟨B, hB⟩ := mβ C hC
      refine ⟨B + |b| * A, fun g u hu => ?_⟩
      have e : (β (g * u) - b * η' (g * u)) - (β g - b * η' g) =
          (β (g * u) - β g) - b * (η' (g * u) - η' g) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hB g u hu) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg b)
    have hl : |x.2 - ε - x.2| ≤ ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]
    have hr : |x.2 + ε - x.2| ≤ ε := by rw [add_sub_cancel_left, abs_of_pos hε]
    obtain ⟨U, hU, u, hu, hb⟩ := GlobalTheory.T.coarse_lipschitz_exponential_estimate G (L →L[ℂ] W) Γ (Γ ⊓ Q) P P' ξ (fun x => a * η x) (fun x => β x - b * η' x) H a b
      (x.2 - ε) (x.2 + ε) M mξ m₁ m₂ (hW.convR a hRa) (hW.convL b hbR) hM
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hl).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hr).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hl).2)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hr).2) g
    refine ⟨Set.Icc b a ×ˢ Set.Icc (x.2 - ε) (x.2 + ε),
      prod_mem_nhds (Icc_mem_nhds hbx hxa) (Icc_mem_nhds (by linarith) (by linarith)), U, hU, u, hu, ?_⟩
    intro l hl g' hg' r
    obtain ⟨h1, h2⟩ := hl
    exact hb l h1.1 h1.2 h2.1 h2.2 g' hg' r
  obtain ⟨hTG, hsum⟩ := GlobalTheory.T.holomorphic_series_uniform_tube _ _ _ t Ω hhol hcont hdom
  have key : ∀ l ∈ tube Ω, ∀ g (w : L), outer Γ (Γ ⊓ Q) ξ H l g w =
      ∑' r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by
    intro l hl g w
    have hs : Summable fun r => t r l g := (hsum l hl g).of_norm
    exact (ContinuousLinearMap.apply ℂ W w).map_tsum hs
  obtain ⟨law, -, Ms, hMs⟩ := hSec G W K ρ hK hρ Γ P c hP
  obtain ⟨law', -, Ms', hMs'⟩ := hSec G W K ρ hK hρ Γ P' c hP'
  refine ⟨hTG, hsum, ?_, ?_⟩
  · intro l hl hRl hconv g w
    have hw : (w : W) ∈ secSp K P c ρ := hW.le w.2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        D l.1 • (Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P c ρ (fun x => l.1 * η x) (rep r * g) w) := by
      intro r
      rw [hW.eqR l.1 hRl, smul_comm]
    simp_rw [e]
    rw [tsum_const_smul'']
    congr 1
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P c ρ ξ (fun x => l.1.re * η x + l.2.re * ξ x) (fun x => l.1 * η x) l.2 w
      (Ms * ‖(w : W)‖) hPQ hξinv ?_ (sec_inv hP (law w hw)) (fun x => hMs x w) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    · intro x
      simp
  · intro l hl hRl hconv g w
    have hw : ((Op l.1 w : secSp K P' c ρ) : W) ∈ secSp K P' c ρ := (Op l.1 w).2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P' c ρ (fun x => β x - l.1 * η' x) (rep r * g) (Op l.1 w) := by
      intro r
      rw [hW.eqL l.1 hRl]
    simp_rw [e]
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P' c ρ ξ (fun x => β x - l.1.re * η' x + l.2.re * ξ x)
      (fun x => (β x : ℂ) - l.1 * η' x) l.2 _ (Ms' * ‖((Op l.1 w : secSp K P' c ρ) : W)‖) hP'Q hξinv ?_
      (sec_inv hP' (law' _ hw)) (fun x => hMs' x _) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    · intro x
      simp
end GlobalTheory.CompanionTheory.RgEisCross
