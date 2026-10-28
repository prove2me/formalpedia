-- Prove2me | solution 1 for LambdaVaRAmb.Robust.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:30:58.527421+00:00
-- url     : https://prove2.me/submissions/a4b57a0f-25d0-41a8-b7ef-0a7ae8f9c767

import Mathlib
import Definitions.Def_LambdaVaRAmb_Robust_Setting
import Theorems.Thm_LambdaVaRAmb_Robust_corollary_1
import Theorems.Thm_LambdaVaRAmb_Robust_proposition_5
import Theorems.Thm_LambdaVaRAmb_Robust_proposition_5_properties

open MeasureTheory Filter Topology LambdaVaRAmb.Robust

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (φ : ℝ → EReal) (hφ : IsPhiFunction φ) :
    (∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) = LVaR Λ (distortedCap φ δ P) X) ∧
    (∀ δ : ℝ, 0 < δ → ∀ α : ℝ, 0 < α → α < 1 → ∀ X : Ω → ℝ, Measurable X →
        (⨆ Q ∈ phiBall φ P δ, VaRw α (probCap Q) X) = VaRw α (distortedCap φ δ P) X) ∧
    ((∀ x : ℝ, 0 ≤ x → φ x ≠ ⊤) →
      StrictConvexOn ℝ (Set.Ici 0) (fun x => (φ x).toReal) →
      Tendsto (fun x => (φ x).toReal / x) atTop atTop →
      (∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
          (⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) = LVaR (gPhiInv φ δ ∘ Λ) (probCap P) X) ∧
      (∀ δ : ℝ, 0 < δ → ∀ α : ℝ, 0 < α → α < 1 → ∀ X : Ω → ℝ, Measurable X →
          (⨆ Q ∈ phiBall φ P δ, VaRw α (probCap Q) X) = VaRw (gPhiInv φ δ α) (probCap P) X) ∧
      (∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
          Tendsto (fun δ => ⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) (𝓝[>] 0)
            (𝓝 (LVaRPlus Λ (probCap P) X)) ∧
          Tendsto (fun δ => LVaR (gPhiInv φ δ ∘ Λ) (probCap P) X) (𝓝[>] 0)
            (𝓝 (LVaRPlus Λ (probCap P) X)))) := by
  -- `ℙ` belongs to every ball of nonnegative radius
  have hPmem : ∀ δ : ℝ, 0 < δ → P ∈ phiBall φ P δ := by
    intro δ hδ
    refine ⟨inferInstance, Measure.AbsolutelyContinuous.rfl, ?_⟩
    have h1 : (∫⁻ ω, (φ (P.rnDeriv P ω).toReal).toENNReal ∂P) = 0 := by
      rw [lintegral_congr_ae ((Measure.rnDeriv_self P).mono fun ω hω => by
        dsimp only; rw [hω]; simp [hφ.map_one] : (fun ω => (φ (P.rnDeriv P ω).toReal).toENNReal) =ᵐ[P]
          fun _ => 0)]
      simp
    have h2 : (∫⁻ ω, (-(φ (P.rnDeriv P ω).toReal)).toENNReal ∂P) = 0 := by
      rw [lintegral_congr_ae ((Measure.rnDeriv_self P).mono fun ω hω => by
        dsimp only; rw [hω]; simp [hφ.map_one] : (fun ω => (-(φ (P.rnDeriv P ω).toReal)).toENNReal) =ᵐ[P]
          fun _ => 0)]
      simp
    unfold phiDiv
    rw [h1, h2]
    simp only [ENNReal.coe_toNNReal, EReal.coe_ennreal_zero, sub_zero]
    exact_mod_cast hδ.le
  have hm : ∀ X : Ω → ℝ, Measurable X → ∀ x : ℝ, MeasurableSet {ω | x < X ω} :=
    fun X hX x => measurableSet_lt measurable_const hX
  have hPr : ∀ A : Set Ω, 0 ≤ P.real A ∧ P.real A ≤ 1 :=
    fun A => ⟨measureReal_nonneg, measureReal_le_one⟩
  -- Part 1
  have part1 : ∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
      (⨆ Q ∈ phiBall φ P δ, LVaR Λ (probCap Q) X) = LVaR Λ (distortedCap φ δ P) X := by
    intro δ hδ Λ hΛ X hX
    have hc := (corollary_1 (phiBall φ P δ) ⟨P, hPmem δ hδ⟩ (fun Q hQ => hQ.1) Λ hΛ).2.2 X hX
    rw [hc.1]
    unfold LVaR
    congr 2
    ext x
    simp only [Set.mem_setOf_eq]
    rw [proposition_5 P φ hφ δ hδ _ (hm X hX x)]
    rfl
  have hconst : ∀ α : ℝ, 0 < α → α < 1 → InHI (fun _ : ℝ => α) :=
    fun α h0 h1 => ⟨fun _ => ⟨h0, h1⟩, monotone_const⟩
  refine ⟨part1, fun δ hδ α h0 h1 X hX => part1 δ hδ _ (hconst α h0 h1) X hX, ?_⟩
  intro hfin hsc hsl
  have props := proposition_5_properties φ hφ hfin hsc hsl
  -- the Galois property of `g⁻¹`
  have key : ∀ δ : ℝ, 0 < δ → ∀ l : ℝ, 0 < l → l < 1 → ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (gPhi φ δ p ≤ l ↔ p ≤ gPhiInv φ δ l) := by
    intro δ hδ l hl0 hl1 p hp0 hp1
    obtain ⟨xδ, hxδ, -, -, hcont, hsmono, hone⟩ := props.1 δ hδ
    set S := {x : ℝ | x ∈ Set.Icc 0 1 ∧ gPhi φ δ x ≤ l} with hS
    have hST : S = Set.Icc 0 xδ ∩ gPhi φ δ ⁻¹' Set.Iic l := by
      ext x
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_Iic]
      constructor
      · rintro ⟨⟨h0, h1⟩, hg⟩
        refine ⟨⟨h0, ?_⟩, hg⟩
        by_contra hx
        push_neg at hx
        have := hone x ⟨hx.le, h1⟩
        linarith
      · rintro ⟨⟨h0, h1⟩, hg⟩
        exact ⟨⟨h0, h1.trans hxδ.2.le⟩, hg⟩
    have hclosed : IsClosed S := by
      rw [hST]; exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have h0S : (0 : ℝ) ∈ S := by
      refine ⟨⟨le_refl _, zero_le_one⟩, ?_⟩
      simp only [gPhi, if_pos rfl]; exact hl0.le
    have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    have hsS : sSup S ∈ S := hclosed.csSup_mem ⟨0, h0S⟩ hbdd
    have hsS' : sSup S ∈ Set.Icc 0 xδ ∩ gPhi φ δ ⁻¹' Set.Iic l := by rw [← hST]; exact hsS
    change gPhi φ δ p ≤ l ↔ p ≤ sSup S
    constructor
    · intro hg; exact le_csSup hbdd ⟨⟨hp0, hp1⟩, hg⟩
    · intro hp
      have hpI : p ∈ Set.Icc 0 xδ := ⟨hp0, hp.trans hsS'.1.2⟩
      exact le_trans (hsmono.monotoneOn hpI hsS'.1 hp) hsS'.2
  have part3 : ∀ δ : ℝ, 0 < δ → ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
      LVaR Λ (distortedCap φ δ P) X = LVaR (gPhiInv φ δ ∘ Λ) (probCap P) X := by
    intro δ hδ Λ hΛ X hX
    unfold LVaR
    congr 2
    ext x
    simp only [Set.mem_setOf_eq, Function.comp]
    exact key δ hδ (Λ x) (hΛ.1 x).1 (hΛ.1 x).2 _ (hPr _).1 (hPr _).2
  have part5 : ∀ Λ : ℝ → ℝ, InHI Λ → ∀ X : Ω → ℝ, Measurable X →
      Tendsto (fun δ => LVaR Λ (distortedCap φ δ P) X) (𝓝[>] 0)
        (𝓝 (LVaRPlus Λ (probCap P) X)) := by
    intro Λ hΛ X hX
    -- every element of `S_δ` lies strictly in `{P(X > x) < Λ x}`
    have hSlt : ∀ δ : ℝ, 0 < δ → ∀ x : ℝ, gPhi φ δ (P.real {ω | x < X ω}) ≤ Λ x →
        P.real {ω | x < X ω} < Λ x := by
      intro δ hδ x hx
      have hp := hPr {ω | x < X ω}
      set p := P.real {ω | x < X ω}
      rcases hp.1.eq_or_lt with h | h
      · rw [← h]; exact (hΛ.1 x).1
      rcases hp.2.eq_or_lt with h' | h'
      · exfalso
        have : gPhi φ δ p = 1 := by
          rw [h']; simp [gPhi]
        linarith [(hΛ.1 x).2]
      · exact lt_of_lt_of_le ((props.2 p ⟨h, h'⟩).1 δ hδ) hx
    rw [tendsto_order]
    constructor
    · intro a ha
      refine eventually_nhdsWithin_of_forall fun δ hδ => lt_of_lt_of_le ha ?_
      apply sSup_le
      rintro _ ⟨y, hy, rfl⟩
      apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_setOf_eq] at hx hy
      have hlt := hSlt δ hδ x hx
      rw [EReal.coe_le_coe_iff]
      by_contra hxy
      push_neg at hxy
      have h1 : P.real {ω | y < X ω} ≤ P.real {ω | x < X ω} :=
        measureReal_mono (fun ω hω => lt_trans hxy hω)
      have h2 := hΛ.2 hxy.le
      unfold probCap at hy
      linarith
    · intro b hb
      obtain ⟨y, hy1, hy2⟩ := EReal.exists_between_coe_real hb
      have hyT : P.real {ω | y < X ω} < Λ y := by
        by_contra hc
        push_neg at hc
        have : (y : EReal) ≤ LVaRPlus Λ (probCap P) X := le_sSup ⟨y, hc, rfl⟩
        exact absurd hy1 (not_lt.2 this)
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), gPhi φ δ (P.real {ω | y < X ω}) ≤ Λ y := by
        rcases (hPr {ω | y < X ω}).1.eq_or_lt with h | h
        · refine eventually_nhdsWithin_of_forall fun δ _ => ?_
          rw [← h]; simp only [gPhi, if_pos rfl]; exact (hΛ.1 y).1.le
        · have hp1 : P.real {ω | y < X ω} < 1 := lt_trans hyT (hΛ.1 y).2
          exact ((props.2 _ ⟨h, hp1⟩).2.2.eventually (gt_mem_nhds hyT)).mono fun δ hδ => hδ.le
      refine hev.mono fun δ hδ => lt_of_le_of_lt ?_ hy2
      exact sInf_le ⟨y, hδ, rfl⟩
  refine ⟨fun δ hδ Λ hΛ X hX => (part1 δ hδ Λ hΛ X hX).trans (part3 δ hδ Λ hΛ X hX),
    fun δ hδ α h0 h1 X hX => (part1 δ hδ _ (hconst α h0 h1) X hX).trans
      (part3 δ hδ _ (hconst α h0 h1) X hX), fun Λ hΛ X hX => ⟨?_, ?_⟩⟩
  · refine (part5 Λ hΛ X hX).congr' ?_
    exact eventually_nhdsWithin_of_forall fun δ hδ => (part1 δ hδ Λ hΛ X hX).symm
  · refine (part5 Λ hΛ X hX).congr' ?_
    exact eventually_nhdsWithin_of_forall fun δ hδ => part3 δ hδ Λ hΛ X hX
