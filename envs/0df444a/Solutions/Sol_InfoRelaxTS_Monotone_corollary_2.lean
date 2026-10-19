-- Prove2me | solution 1 for InfoRelaxTS.Monotone.corollary_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T10:14:38.47444+00:00
-- url     : https://prove2.me/submissions/73ffb734-380c-4b80-be34-8648b9bce56e

-- Direction: Alexander Richard Towell (queelius); formalization: OpenAI Codex.
-- Source: Seungki Min, Costis Maglaras, Ciamac C. Moallemi, arXiv1902.04251v2.
-- Platform formulation: mikedeng1; statement review: Shuze Chen. Lean/Mathlib foundations.
import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace MonotoneJensen
lemma below (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : c+φ c ≤ 0) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0 := by
  by_cases hx : x ≤ c
  · have h := hφ hx
    rw [max_eq_right (show c+φ x ≤ 0 by linarith)]
    exact le_max_right _ _
  · exact max_le_max (by linarith [lt_of_not_ge hx]) le_rfl
lemma above (φ : ℝ → ℝ) (hφ : Monotone φ) (c : ℝ) (hc : 0 ≤ c+φ c) (x : ℝ) :
    max (c+φ x) 0 ≤ max (x+φ x) 0-x+c := by
  by_cases hx : x ≤ c
  · apply max_le
    · have h := le_max_left (x+φ x) 0;linarith
    · have h := le_max_right (x+φ x) 0;linarith
  · have h := hφ (le_of_not_ge hx)
    rw [max_eq_left (show 0 ≤ c+φ x by linarith),max_eq_left (show 0 ≤ x+φ x by linarith)]
    linarith
end MonotoneJensen

theorem monotone_jensen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : ℝ → ℝ) (hφ : Monotone φ) (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((∫ ω', X ω' ∂μ) + φ (X ω)) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω)) 0) ∂μ := by
  let c := ∫ ω, X ω ∂μ
  let A := fun ω => max (X ω+φ (X ω)) 0
  let B := fun ω => max (c+φ (X ω)) 0
  change (∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (A ω) ∂μ
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (A ω) ∂μ)=⊤
  · rw [htop];exact le_top
  have hp : AEMeasurable (fun ω => φ (X ω)) μ := hφ.measurable.comp_aemeasurable hX.aemeasurable
  have hAm : AEStronglyMeasurable A μ := ((hX.aemeasurable.add hp).max aemeasurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B μ := ((aemeasurable_const.add hp).max aemeasurable_const).aestronglyMeasurable
  have hAn : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hBn : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hAi : Integrable A μ := (lintegral_ofReal_ne_top_iff_integrable hAm hAn).mp htop
  rcases le_total (c+φ c) 0 with hc | hc
  · apply lintegral_mono
    intro ω
    exact ENNReal.ofReal_le_ofReal (MonotoneJensen.below φ hφ c hc (X ω))
  · have hbound : ∀ ω, B ω ≤ A ω-X ω+c := fun ω => MonotoneJensen.above φ hφ c hc (X ω)
    have hCi : Integrable (fun ω => A ω-X ω+c) μ := (hAi.sub hX).add (integrable_const c)
    have hBi : Integrable B μ := hCi.mono' hBm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right (c+φ (X ω)) 0)]
      exact hbound ω)
    have hInt := integral_mono_ae hBi hCi (Filter.Eventually.of_forall hbound)
    have hcancel : (∫ ω, A ω-X ω+c ∂μ)=∫ ω, A ω ∂μ := by
      calc
        (∫ ω, A ω-X ω+c ∂μ) = (∫ ω, A ω-X ω ∂μ)+(∫ _ : Ω, c ∂μ) :=
          integral_add (hAi.sub hX) (integrable_const c)
        _ = ∫ ω, A ω ∂μ := by rw [integral_sub hAi hX];simp [c]
    rw [hcancel] at hInt
    rw [← ofReal_integral_eq_lintegral_ofReal hBi hBn,← ofReal_integral_eq_lintegral_ofReal hAi hAn]
    exact ENNReal.ofReal_le_ofReal hInt
namespace MonotoneJensen
lemma conditional {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (φ : ℝ → Ω → ℝ) (hmono : ∀ ω, Monotone fun x => φ x ω)
    (hmeas : ∀ x, Measurable[mH] (φ x))
    (hjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ))
    (X : Ω → ℝ) (hX : Integrable X μ) :
    ∫⁻ ω, ENNReal.ofReal (max ((μ[X | mH]) ω + φ (X ω) ω) 0) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (max (X ω + φ (X ω) ω) 0) ∂μ := by
  let c := μ[X | mH]
  let A := fun ω => max (X ω+φ (X ω) ω) 0
  let B := fun ω => max (c ω+φ (X ω) ω) 0
  let S := {ω | 0 ≤ c ω+φ (c ω) ω}
  let Z := S.indicator (fun ω => X ω-c ω)
  have hId : @Measurable Ω Ω mΩ mH id := measurable_id'' hmH
  have hcH : Measurable[mH] c := stronglyMeasurable_condExp.measurable
  have hφc : Measurable[mH] (fun ω => φ (c ω) ω) := hjoint.comp (hcH.prodMk measurable_id)
  have hS : MeasurableSet[mH] S := measurableSet_le measurable_const (hcH.add hφc)
  have hjfull : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mΩ) _ (Function.uncurry φ) :=
    hjoint.mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono hmH)) le_rfl
  have hφx : AEMeasurable (fun ω => φ (X ω) ω) μ :=
    hjfull.comp_aemeasurable (hX.aemeasurable.prodMk aemeasurable_id)
  have hc : Integrable c μ := integrable_condExp
  have hAm : AEStronglyMeasurable A μ := ((hX.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hBm : AEStronglyMeasurable B μ := ((hc.aemeasurable.add hφx).max aemeasurable_const).aestronglyMeasurable
  have hZn : Integrable Z μ := (hX.sub hc).indicator (hmH S hS)
  have hZint : (∫ ω, Z ω ∂μ)=0 := by
    dsimp [Z]
    rw [integral_indicator (hmH S hS),integral_sub hX.integrableOn hc.integrableOn,
      setIntegral_condExp hmH hX hS]
    ring
  have hbound (ω) : B ω ≤ A ω-Z ω := by
    by_cases hs : ω ∈ S
    · rw [show Z ω=X ω-c ω from Set.indicator_of_mem hs _]
      have h := above (fun x => φ x ω) (hmono ω) (c ω) hs (X ω)
      dsimp [A,B]
      linarith
    · rw [show Z ω=0 from Set.indicator_of_notMem hs _,sub_zero]
      exact below (fun x => φ x ω) (hmono ω) (c ω) (le_of_not_ge hs) (X ω)
  change (∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) ≤ ∫⁻ ω, ENNReal.ofReal (A ω) ∂μ
  by_cases htop : (∫⁻ ω, ENNReal.ofReal (A ω) ∂μ)=⊤
  · rw [htop];exact le_top
  have hAn : 0 ≤ᵐ[μ] A := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hBn : 0 ≤ᵐ[μ] B := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hAi := (lintegral_ofReal_ne_top_iff_integrable hAm hAn).mp htop
  have hBi : Integrable B μ := (hAi.sub hZn).mono' hBm (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right (c ω+φ (X ω) ω) 0)]
    exact hbound ω)
  have hInt := integral_mono_ae hBi (hAi.sub hZn) (Filter.Eventually.of_forall hbound)
  have hcancel : (∫ ω, (A-Z) ω ∂μ)=∫ ω, A ω ∂μ := by
    change (∫ ω, A ω-Z ω ∂μ)=∫ ω, A ω ∂μ
    rw [integral_sub hAi hZn,hZint,sub_zero]
  rw [hcancel] at hInt
  rw [← ofReal_integral_eq_lintegral_ofReal hBi hBn,← ofReal_integral_eq_lintegral_ofReal hAi hAn]
  exact ENNReal.ofReal_le_ofReal hInt
end MonotoneJensen
namespace MonotoneJensen
lemma integrable_iSup {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun ω => ⨆ i, f i ω) μ := by
  classical
  have h : Integrable (Finset.univ.sup' Finset.univ_nonempty f) μ :=
    Finset.sup'_induction Finset.univ_nonempty f (p := fun g => Integrable g μ)
      (fun a ha b hb => ha.sup hb) (fun i _ => hf i)
  convert h using 1
  funext ω
  simp only [Finset.sup'_apply,Finset.sup'_univ_eq_ciSup]
lemma split_sup {ι : Type*} [Fintype ι] [Nonempty ι] (P : ι → Prop) [DecidablePred P]
    [Nonempty {i // P i}] [Nonempty {i // ¬P i}] (a b : ι → ℝ) (c : ℝ) :
    (⨆ i, if P i then a i else c+b i)=max (⨆ i : {i // P i},a i) (c+⨆ i : {i // ¬P i},b i) := by
  have hbound (f : ι → ℝ) : BddAbove (Set.range f) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · apply ciSup_le
    intro i
    split_ifs with hi
    · have h : a i ≤ ⨆ j : {j // P j}, a j :=
        le_ciSup (f := fun j : {j // P j} => a j) (Set.finite_range _).bddAbove ⟨i,hi⟩
      exact h.trans (le_max_left _ _)
    · have h : b i ≤ ⨆ j : {j // ¬P j}, b j :=
        le_ciSup (f := fun j : {j // ¬P j} => b j) (Set.finite_range _).bddAbove ⟨i,hi⟩
      exact (add_le_add_right h c).trans (le_max_right _ _)
  · apply max_le
    · apply ciSup_le
      intro i
      have h := le_ciSup (hbound (fun i => if P i then a i else c+b i)) i.val
      simpa only [if_pos i.property] using h
    · apply (le_sub_iff_add_le').mp
      apply ciSup_le
      intro i
      have h := le_ciSup (hbound (fun i => if P i then a i else c+b i)) i.val
      rw [if_neg i.property] at h
      linarith
lemma max_shift (a b c : ℝ) : max a (c+b)=max (c+(b-a)) 0+a := by
  by_cases h : a ≤ c+b
  · rw [max_eq_right h,max_eq_left (show 0 ≤ c+(b-a) by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (show c+(b-a) ≤ 0 by linarith)]
    ring
lemma nat_step (i n : ℕ) : ((i-n : ℕ) : ℝ) =
    (if n+1 ≤ i then (1 : ℝ) else 0)+((i-n-1 : ℕ) : ℝ) := by
  by_cases hi : n+1 ≤ i
  · rw [if_pos hi]
    have h : i-n=(i-n-1)+1 := by omega
    calc
      ((i-n : ℕ) : ℝ) = ((i-n-1+1 : ℕ) : ℝ) := congrArg Nat.cast h
      _ = 1+((i-n-1 : ℕ) : ℝ) := by push_cast; ring
  · have h : i ≤ n := by omega
    simp [Nat.sub_eq_zero_of_le h,hi]
lemma finite_max {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (T : ℕ) (C : Fin (T+1) → Ω → ℝ) (hCmeas : ∀ i, Measurable[mH] (C i))
    (hCint : ∀ i, Integrable (C i) μ) (X : Ω → ℝ) (hX : Integrable X μ) (n : ℕ) (hn : n ≤ T) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T+1) =>
      (μ[X|mH]) ω*(if n+1 ≤ (i : ℕ) then (1 : ℝ) else 0)+(((i : ℕ)-n-1 : ℕ) : ℝ)*X ω+C i ω) ∂μ) ≤
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T+1) =>
      (((i : ℕ)-n : ℕ) : ℝ)*X ω+C i ω) ∂μ := by
  classical
  by_cases he : n=T
  · subst n
    have hi (i : Fin (T+1)) : (i : ℕ) ≤ T := by omega
    have hno (i : Fin (T+1)) : ¬T+1 ≤ (i : ℕ) := by omega
    simp only [Nat.sub_eq_zero_of_le (hi _),Nat.zero_sub,Nat.cast_zero,zero_mul,add_zero,
      if_neg (hno _),mul_zero,zero_add,le_refl]
  have hnT : n < T := lt_of_le_of_ne hn he
  let P := fun i : Fin (T+1) => (i : ℕ) ≤ n
  letI : Nonempty {i // P i} := ⟨⟨⟨0,by omega⟩,by dsimp [P];omega⟩⟩
  letI : Nonempty {i // ¬P i} := ⟨⟨⟨n+1,by omega⟩,by dsimp [P];omega⟩⟩
  let L := fun ω => ⨆ i : {i // P i}, C i ω
  let U := fun z ω => ⨆ i : {i // ¬P i}, (((i.val : ℕ)-n-1 : ℕ) : ℝ)*z+C i ω
  let φ := fun z ω => U z ω-L ω
  have hmono : ∀ ω, Monotone fun z => φ z ω := by
    intro ω a b hab
    apply sub_le_sub_right
    apply ciSup_le
    intro i
    apply le_trans _ (le_ciSup (Set.finite_range _).bddAbove i)
    have h := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg ((i.val : ℕ)-n-1) : (0 : ℝ) ≤ _)
    linarith
  have hLm : Measurable[mH] L := Measurable.iSup (fun i => hCmeas i)
  have hφm : ∀ z, Measurable[mH] (φ z) := by
    intro z
    exact (Measurable.iSup (fun i : {i // ¬P i} =>
      (measurable_const (a := (((i.val : ℕ)-n-1 : ℕ) : ℝ)*z)).add (hCmeas i))).sub hLm
  have hφjoint : @Measurable (ℝ × Ω) ℝ (@Prod.instMeasurableSpace ℝ Ω _ mH) _ (Function.uncurry φ) := by
    letI := mH
    exact (Measurable.iSup (fun i : {i // ¬P i} =>
      (measurable_const.mul measurable_fst).add ((hCmeas i).comp measurable_snd))).sub (hLm.comp measurable_snd)
  have hLi : Integrable L μ := integrable_iSup μ _ (fun i => hCint i)
  have hUi : Integrable (fun ω => U (X ω) ω) μ := integrable_iSup μ _
    (fun i => (hX.const_mul (((i.val : ℕ)-n-1 : ℕ) : ℝ)).add (hCint i))
  have hφi : Integrable (fun ω => φ (X ω) ω) μ := hUi.sub hLi
  have hc : Integrable (μ[X|mH]) μ := integrable_condExp
  have hAi : Integrable (fun ω => max (X ω+φ (X ω) ω) 0) μ := (hX.add hφi).sup (integrable_const 0)
  have hBi : Integrable (fun ω => max ((μ[X|mH]) ω+φ (X ω) ω) 0) μ := (hc.add hφi).sup (integrable_const 0)
  have hineq := conditional hmH μ φ hmono hφm hφjoint X hX
  rw [← ofReal_integral_eq_lintegral_ofReal hBi (Filter.Eventually.of_forall fun _ => le_max_right _ _),
    ← ofReal_integral_eq_lintegral_ofReal hAi (Filter.Eventually.of_forall fun _ => le_max_right _ _)] at hineq
  have hreal : (∫ ω, max ((μ[X|mH]) ω+φ (X ω) ω) 0 ∂μ) ≤ ∫ ω, max (X ω+φ (X ω) ω) 0 ∂μ := by
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => le_max_right _ _)).mp hineq
  have hsplit (z c : ℝ) (ω : Ω) :
      Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T+1) =>
        c*(if n+1 ≤ (i : ℕ) then (1 : ℝ) else 0)+(((i : ℕ)-n-1 : ℕ) : ℝ)*z+C i ω)
        = max (c+φ z ω) 0+L ω := by
    rw [Finset.sup'_univ_eq_ciSup]
    have hfun : (fun i : Fin (T+1) => c*(if n+1 ≤ (i : ℕ) then (1 : ℝ) else 0)+(((i : ℕ)-n-1 : ℕ) : ℝ)*z+C i ω)=
        (fun i => if P i then C i ω else c+(((i : ℕ)-n-1 : ℕ) : ℝ)*z+C i ω) := by
      funext i
      by_cases hi : P i
      · have hle : (i : ℕ) ≤ n := hi
        simp [hi,show ¬n+1 ≤ (i : ℕ) by omega,Nat.sub_eq_zero_of_le hle]
      · have hle : n+1 ≤ (i : ℕ) := by dsimp [P] at hi;omega
        simp [hi,hle]
    rw [hfun]
    have he := split_sup P (fun i => C i ω) (fun i => (((i : ℕ)-n-1 : ℕ) : ℝ)*z+C i ω) c
    simpa only [add_assoc] using he.trans (max_shift (L ω) (U z ω) c)
  have horig (ω : Ω) : Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T+1) =>
      (((i : ℕ)-n : ℕ) : ℝ)*X ω+C i ω)=max (X ω+φ (X ω) ω) 0+L ω := by
    rw [← hsplit (X ω) (X ω) ω]
    congr 1
    funext i
    rw [nat_step]
    ring
  simp_rw [hsplit,horig]
  rw [integral_add hBi hLi,integral_add hAi hLi]
  linarith
end MonotoneJensen


open MeasureTheory ProbabilityTheory

/-- Corollary 2, pp. 57–58, (142): for `ℋ`-measurable integrable `C_0, …, C_T`, integrable `X` and
`n ∈ {0, …, T}`,
`𝔼[max_{0≤i≤T} {(i − n)⁺ X + C_i}] ≥ 𝔼[max_{0≤i≤T} {𝔼(X|ℋ)·1{i ≥ n+1} + (i − n − 1)⁺ X + C_i}]`.
The positive parts `(i − n)⁺`, `(i − n − 1)⁺` are natural-number subtractions. -/
theorem solution {Ω : Type*} {mH mΩ : MeasurableSpace Ω} (hmH : mH ≤ mΩ)
    (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ]
    (T : ℕ) (C : Fin (T + 1) → Ω → ℝ) (hCmeas : ∀ i, Measurable[mH] (C i))
    (hCint : ∀ i, Integrable (C i) μ) (X : Ω → ℝ) (hX : Integrable X μ) (n : ℕ) (hn : n ≤ T) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T + 1) =>
        (μ[X | mH]) ω * (if n + 1 ≤ (i : ℕ) then (1 : ℝ) else 0)
          + (((i : ℕ) - n - 1 : ℕ) : ℝ) * X ω + C i ω) ∂μ
      ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (T + 1) =>
        (((i : ℕ) - n : ℕ) : ℝ) * X ω + C i ω) ∂μ := by
  exact MonotoneJensen.finite_max hmH μ T C hCmeas hCint X hX n hn


