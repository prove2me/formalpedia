-- Prove2me | solution 1 for LimitPoA.RegVar.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:00:34.876336+00:00
-- url     : https://prove2.me/submissions/a4ce252f-8fb9-4971-abd2-e8f5019957cc

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_LimitPoA_RegVar_Model
import Definitions.Def_LimitPoA_RegVar_Limit

open Filter Topology LimitPoA.RegVar KellyStochasticNetworks

/-- Every unbounded demand sequence has a regular subsequence. -/
lemma exists_regular_subseq (Γ : Game) (e : ℕ → Fin Γ.Sd → ℝ) (he : IsUnbounded Γ e) :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧ ∃ dInf, IsRegular Γ (e ∘ χ) dInf := by
  obtain ⟨hnn, hT⟩ := he
  let x : ℕ → (Fin Γ.Sd → EReal) × (Fin Γ.Sd → ℝ) :=
    fun n => (fun k => ((e n k : ℝ) : EReal), fun k => e n k / totalDemand Γ (e n))
  let s : Set ((Fin Γ.Sd → EReal) × (Fin Γ.Sd → ℝ)) :=
    Set.univ ×ˢ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hs : IsCompact s := isCompact_univ.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hx : ∀ n, x n ∈ s := by
    intro n
    refine ⟨Set.mem_univ _, fun k _ => ?_⟩
    have h0 : 0 ≤ totalDemand Γ (e n) := Finset.sum_nonneg fun k _ => hnn n k
    show 0 ≤ e n k / totalDemand Γ (e n) ∧ e n k / totalDemand Γ (e n) ≤ 1
    refine ⟨div_nonneg (hnn n k) h0, ?_⟩
    rcases h0.eq_or_lt with h | h
    · rw [← h, div_zero]; exact zero_le_one
    · rw [div_le_one h]
      exact Finset.single_le_sum (f := fun k => e n k) (fun k _ => hnn n k) (Finset.mem_univ k)
  obtain ⟨⟨L, dInf⟩, -, χ, hχ, hlim⟩ := hs.tendsto_subseq hx
  refine ⟨χ, hχ, dInf, ⟨⟨fun n k => hnn _ k, hT.comp hχ.tendsto_atTop⟩, fun k => ?_, fun k => ?_⟩⟩
  · have hk : Tendsto (fun n => ((e (χ n) k : ℝ) : EReal)) atTop (𝓝 (L k)) :=
      ((continuous_apply k).tendsto _).comp ((continuous_fst.tendsto _).comp hlim)
    induction hL : L k using EReal.rec with
    | bot =>
      rw [hL, EReal.tendsto_coe_nhds_bot_iff] at hk
      exfalso
      obtain ⟨n, hn⟩ := (hk.eventually (eventually_lt_atBot (0 : ℝ))).exists
      exact absurd (hnn _ k) (not_le.mpr hn)
    | coe r =>
      rw [hL, EReal.tendsto_coe] at hk
      exact Or.inr ⟨r, hk⟩
    | top =>
      rw [hL, EReal.tendsto_coe_nhds_top_iff] at hk
      exact Or.inl hk
  · exact ((continuous_apply k).tendsto _).comp ((continuous_snd.tendsto _).comp hlim)

theorem solution (Γ : Game) (hΓ : Γ.Standing) (τ : Fin Γ.J → ℝ → ℝ)
    (hτ : ∀ a, IsCostFn (τ a)) (hnd : ∀ a, ∃ x, 0 < x ∧ τ a x ≠ 0) :
    List.TFAE
      [IsAsymptoticallyWellDesigned Γ τ,
       ∀ (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ), IsRegular Γ d dInf →
         Tendsto (fun n => PoA Γ τ (d n)) atTop (𝓝 1),
       ∀ (d : ℕ → Fin Γ.Sd → ℝ) (dInf : Fin Γ.Sd → ℝ), IsRegular Γ d dInf →
         ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun i => PoA Γ τ (d (φ i))) atTop (𝓝 1)] := by
  tfae_have 1 → 2 := fun h d dInf hreg => h d hreg.1
  tfae_have 2 → 3 := fun h d dInf hreg => ⟨id, strictMono_id, h d dInf hreg⟩
  tfae_have 3 → 1 := by
    intro h d hd
    by_contra hcon
    rw [tendsto_nhds] at hcon
    push_neg at hcon
    obtain ⟨U, hUo, h1U, hfreq⟩ := hcon
    have hfr : ∃ᶠ n in atTop, PoA Γ τ (d n) ∉ U := by
      intro hev
      apply hfreq
      filter_upwards [hev] with n hn
      simpa using hn
    obtain ⟨ψ, hψ, hψU⟩ := extraction_of_frequently_atTop hfr
    have hdψ : IsUnbounded Γ (d ∘ ψ) :=
      ⟨fun n k => hd.1 _ k, hd.2.comp hψ.tendsto_atTop⟩
    obtain ⟨χ, hχ, dInf, hreg⟩ := exists_regular_subseq Γ (d ∘ ψ) hdψ
    obtain ⟨φ, hφ, hlim⟩ := h _ dInf hreg
    obtain ⟨i, hi⟩ := ((hlim.eventually (hUo.mem_nhds h1U))).exists
    exact hψU _ hi
  tfae_finish
