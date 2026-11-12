-- Prove2me | solution 1 for LuoSunLiu.DIP.proposition_3_conditional
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T04:55:14.034232+00:00
-- url     : https://prove2.me/submissions/b53926a9-f67e-4341-844e-11a596c82a78

import Mathlib
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Theorems.Thm_LuoSunLiu_DIP_proposition_3

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace LuoSunLiu.DIP.P3CondAux

section Kernel
variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

theorem setLIntegral_cek (hm : m ≤ mΩ) {C S : Set Ω}
    (hC : MeasurableSet[m] C) (hS : MeasurableSet S) :
    ∫⁻ a in C, condExpKernel P m a S ∂(P.trim hm) = P (C ∩ S) := by
  have h2 := @Measure.compProd_apply_prod Ω Ω m mΩ (P.trim hm) (condExpKernel P m) _ _ C S hC hS
  rw [← h2, compProd_trim_condExpKernel hm]
  have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
    (measurable_id'' hm).prodMk measurable_id
  rw [@Measure.map_apply Ω (Ω × Ω) mΩ (m.prod mΩ) P Function.diag hdiag _
    (@MeasurableSet.prod Ω Ω m mΩ C S hC hS)]
  rfl

/-- Pair identity: if `A` is independent of `σ(B) ∨ m` then `κ(A ∩ B) = P(A) κ(B)` a.e. -/
theorem pair_ae (hm : m ≤ mΩ) {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hind : ∀ C, MeasurableSet[m] C → P (A ∩ (C ∩ B)) = P A * P (C ∩ B)) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a (A ∩ B) = P A * condExpKernel P m a B := by
  have hf := measurable_condExpKernel (μ := P) (m := m) (hA.inter hB)
  have hg := (measurable_condExpKernel (μ := P) (m := m) hB).const_mul (P A)
  refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m (P.trim hm) _ _ _ hf hg ?_
  intro C hC _
  rw [setLIntegral_cek hm hC (hA.inter hB), lintegral_const_mul _ (measurable_condExpKernel hB),
    setLIntegral_cek hm hC hB, ← hind C hC]
  congr 1; ext ω; simp only [Set.mem_inter_iff]; tauto

theorem self_ae (hm : m ≤ mΩ) {D : Set Ω} (hD : MeasurableSet[m] D) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a D = D.indicator 1 a := by
  have hf := measurable_condExpKernel (μ := P) (m := m) (hm _ hD)
  have hg : Measurable[m] (D.indicator (1 : Ω → ℝ≥0∞)) :=
    Measurable.indicator (m := m) (@measurable_one ℝ≥0∞ Ω _ m _) hD
  refine @ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite Ω m (P.trim hm) _ _ _ hf hg ?_
  intro C hC _
  rw [setLIntegral_cek hm hC (hm _ hD), lintegral_indicator hD, Pi.one_def, setLIntegral_const,
    one_mul, Measure.restrict_apply hD, trim_measurableSet_eq hm (hD.inter hC), Set.inter_comm]


theorem countable_generatePiSystem {α : Type*} {S : Set (Set α)} (hS : S.Countable) :
    (generatePiSystem S).Countable := by
  have : Countable S := hS.to_subtype
  refine (Set.countable_range (fun F : Finset S => ⋂ s ∈ F, (s : Set α))).mono ?_
  intro t ht
  induction ht with
  | base h_s => exact ⟨{⟨_, h_s⟩}, by simp⟩
  | inter _ _ _ h1 h2 =>
    obtain ⟨F, rfl⟩ := h1
    obtain ⟨G, rfl⟩ := h2
    classical
    refine ⟨F ∪ G, ?_⟩
    simp only [Finset.mem_union]
    ext ω; simp only [Set.mem_iInter, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
    · rintro ⟨h1, h2⟩ s (hs | hs)
      · exact h1 s hs
      · exact h2 s hs

omit mΩ [StandardBorelSpace Ω] in
theorem exists_countable_pi {E : Type*} [mE : MeasurableSpace E]
    [MeasurableSpace.CountablyGenerated E] (Y : Ω → E) :
    ∃ p : Set (Set Ω), p.Countable ∧ IsPiSystem p ∧
      MeasurableSpace.comap Y mE = MeasurableSpace.generateFrom p := by
  refine ⟨generatePiSystem (Set.preimage Y '' MeasurableSpace.countableGeneratingSet E),
    countable_generatePiSystem
      (MeasurableSpace.countable_countableGeneratingSet.image _),
    isPiSystem_generatePiSystem _, ?_⟩
  rw [generateFrom_generatePiSystem_eq, ← MeasurableSpace.comap_generateFrom,
    MeasurableSpace.generateFrom_countableGeneratingSet]

theorem ci_ae (hm : m ≤ mΩ) (Z : Ω → ℝ) (hZ : Measurable Z) {E : Type*}
    [mE : MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (Y : Ω → E)
    (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Z inferInstance) (MeasurableSpace.comap Y mE ⊔ m) P) :
    ∀ᵐ a ∂(P.trim hm), Indep (MeasurableSpace.comap Z inferInstance) (MeasurableSpace.comap Y mE)
        (condExpKernel P m a) ∧
      ∀ c : ℝ, (condExpKernel P m a).real {ω | Z ω ≤ c} = P.real {ω | Z ω ≤ c} := by
  obtain ⟨p2, hp2c, hp2pi, hp2eq⟩ := exists_countable_pi (Ω := Ω) Y
  have hp2meas : ∀ B ∈ p2, MeasurableSet B := fun B hB =>
    hY.comap_le _ (hp2eq ▸ MeasurableSpace.measurableSet_generateFrom hB)
  have hp2meas' : ∀ B ∈ p2, MeasurableSet[MeasurableSpace.comap Y mE] B := fun B hB =>
    hp2eq ▸ MeasurableSpace.measurableSet_generateFrom hB
  have hA : ∀ q : ℚ, MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' Set.Iic (q : ℝ)) :=
    fun q => ⟨_, measurableSet_Iic, rfl⟩
  have hAm : ∀ q : ℚ, MeasurableSet (Z ⁻¹' Set.Iic (q : ℝ)) := fun q => hZ measurableSet_Iic
  have key : ∀ q : ℚ, ∀ B : Set Ω, MeasurableSet[MeasurableSpace.comap Y mE] B →
      ∀ᵐ a ∂(P.trim hm), condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ) ∩ B) =
        P (Z ⁻¹' Set.Iic (q : ℝ)) * condExpKernel P m a B := by
    intro q B hB
    refine pair_ae hm (hAm q) (hY.comap_le _ hB) fun C hC => ?_
    exact (Indep_iff _ _ _).1 hind _ _ (hA q) (MeasurableSet.inter
      ((le_sup_right : m ≤ MeasurableSpace.comap Y mE ⊔ m) _ hC)
      ((le_sup_left : MeasurableSpace.comap Y mE ≤ MeasurableSpace.comap Y mE ⊔ m) _ hB))
  have : Countable p2 := hp2c.to_subtype
  have h1 : ∀ᵐ a ∂(P.trim hm), ∀ q : ℚ, ∀ B : p2,
      condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ) ∩ B) =
        P (Z ⁻¹' Set.Iic (q : ℝ)) * condExpKernel P m a B :=
    ae_all_iff.2 fun q => ae_all_iff.2 fun B => key q B (hp2meas' B B.2)
  have h2 : ∀ᵐ a ∂(P.trim hm), ∀ q : ℚ,
      condExpKernel P m a (Z ⁻¹' Set.Iic (q : ℝ)) = P (Z ⁻¹' Set.Iic (q : ℝ)) :=
    ae_all_iff.2 fun q => by
      filter_upwards [key q Set.univ MeasurableSet.univ] with a ha
      simpa using ha
  filter_upwards [h1, h2] with a ha1 ha2
  constructor
  · have hp1pi := (Real.isPiSystem_Iic_rat).comap Z
    refine IndepSets.indep (hZ.comap_le) (hY.comap_le) hp1pi hp2pi ?_ hp2eq ?_
    · have hb : (inferInstance : MeasurableSpace ℝ) =
          MeasurableSpace.generateFrom (⋃ a : ℚ, {Set.Iic (a : ℝ)}) := by
        rw [← Real.borel_eq_generateFrom_Iic_rat]; exact BorelSpace.measurable_eq
      rw [hb, MeasurableSpace.comap_generateFrom]
      rfl
    · rw [IndepSets_iff]
      rintro t1 t2 ⟨t, ht, rfl⟩ ht2
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at ht
      obtain ⟨q, rfl⟩ := ht
      rw [ha1 q ⟨t2, ht2⟩, ha2 q]
  · have hmap : Measure.map Z (condExpKernel P m a) = Measure.map Z P := by
      refine ext_of_generate_finite _ Real.borel_eq_generateFrom_Iic_rat Real.isPiSystem_Iic_rat
        ?_ (by simp [Measure.map_apply hZ MeasurableSet.univ])
      intro s hs
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
      obtain ⟨q, rfl⟩ := hs
      rw [Measure.map_apply hZ measurableSet_Iic, Measure.map_apply hZ measurableSet_Iic, ha2 q]
    intro c
    have := congrArg (fun μ => μ.real (Set.Iic c)) hmap
    rwa [map_measureReal_apply hZ measurableSet_Iic, map_measureReal_apply hZ measurableSet_Iic]
      at this


omit mΩ [StandardBorelSpace Ω] in
theorem setD_meas [mm : MeasurableSpace Ω] {d : ℕ} (θ : Ω → Fin d → ℝ) (hθ : Measurable θ)
    (i : Fin d) (q : ℚ) : MeasurableSet {ω | θ ω i ≤ q} :=
  measurableSet_le ((measurable_pi_apply i).comp hθ) measurable_const

theorem fiber_null (hm : m ≤ mΩ) {d : ℕ} (θ : Ω → Fin d → ℝ) (hθ : Measurable[m] θ) :
    ∀ᵐ a ∂(P.trim hm), condExpKernel P m a {ω | θ ω ≠ θ a} = 0 := by
  have hD : ∀ (i : Fin d) (q : ℚ), MeasurableSet[m] {ω | θ ω i ≤ q} := fun i q =>
    setD_meas (mm := m) θ hθ i q
  have h : ∀ᵐ a ∂(P.trim hm), ∀ (i : Fin d) (q : ℚ),
      condExpKernel P m a {ω | θ ω i ≤ q} = Set.indicator {ω | θ ω i ≤ q} 1 a :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun q => self_ae hm (hD i q)
  filter_upwards [h] with a ha
  have hS : ∀ (i : Fin d) (q : ℚ), condExpKernel P m a
      (if θ a i ≤ q then {ω | θ ω i ≤ q}ᶜ else {ω | θ ω i ≤ q}) = 0 := by
    intro i q
    split_ifs with hq
    · rw [prob_compl_eq_one_sub (hm _ (hD i q)), ha i q, Set.indicator_of_mem (by exact hq)]
      simp
    · rw [ha i q, Set.indicator_of_notMem (by exact hq)]
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun q => hS i q)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  obtain ⟨i, hi⟩ : ∃ i, θ ω i ≠ θ a i := by
    by_contra hc; push Not at hc; exact hω (funext hc)
  simp only [Set.mem_iUnion]
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne hi with hlt | hlt
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, ?_⟩
    rw [if_neg (not_le.2 hq2)]
    exact hq1.le
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
    refine ⟨q, ?_⟩
    rw [if_pos hq1.le]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    exact hq2

end Kernel

section Shift
open LuoSunLiu.DIP

theorem pullSet_shift {d : ℕ} (j : ℕ → Fin d) (s0 τ : ℕ) (i : Fin d) :
    pullSet j s0 τ i = (pullSet (fun t => j (s0 + t)) 0 τ i).map (addLeftEmbedding s0) := by
  ext s
  simp only [pullSet, Finset.mem_filter, Finset.mem_Ico, Finset.mem_map, addLeftEmbedding_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨s - s0, ⟨⟨by omega, by omega⟩, by rw [show s0 + (s - s0) = s by omega]; exact h3⟩,
      by omega⟩
  · rintro ⟨u, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨⟨by omega, by omega⟩, h3⟩

theorem ucb_shift {d : ℕ} (lam β : ℝ) (j : ℕ → Fin d) (p y : ℕ → ℝ) (s0 τ : ℕ) (i : Fin d) :
    ucb lam β j p y s0 τ i =
      ucb lam β (fun t => j (s0 + t)) (fun t => p (s0 + t)) (fun t => y (s0 + t)) 0 τ i := by
  simp only [ucb, pullSet_shift j s0 τ i, Finset.sum_map, addLeftEmbedding_apply]

theorem innerB_shift {d0 d : ℕ} (pmax : ℝ) (θh : Fin d0 → ℝ) (lam : ℝ) (β : ℕ → ℝ) (s0 T0 : ℕ)
    (x : ℕ → Fin d0 → ℝ) (j : ℕ → Fin d) (p y : ℕ → ℝ)
    (h : IsInnerBRun pmax θh lam β s0 T0 x j p y) :
    IsInnerBRun pmax θh lam β 0 T0 (fun t => x (s0 + t)) (fun t => j (s0 + t))
      (fun t => p (s0 + t)) (fun t => y (s0 + t)) := by
  intro τ hτ
  obtain ⟨h1, h2, h3, h4⟩ := h τ hτ
  simp only [zero_add]
  have hpe : ∀ i, pullSet j s0 τ i = ∅ ↔ pullSet (fun t => j (s0 + t)) 0 τ i = ∅ := by
    intro i; rw [pullSet_shift]; simp
  have hpn : ∀ i, (pullSet j s0 τ i).Nonempty ↔ (pullSet (fun t => j (s0 + t)) 0 τ i).Nonempty := by
    intro i; rw [pullSet_shift]; simp
  refine ⟨h1, h2, ?_, ?_⟩
  · rintro ⟨i, hi, he⟩
    exact (hpe _).1 (h3 ⟨i, hi, (hpe i).2 he⟩)
  · intro hall i hi
    have := h4 (fun i hi => (hpn i).2 (hall i hi)) i hi
    rwa [ucb_shift lam (β τ) j p y s0 τ i, ucb_shift lam (β τ) j p y s0 τ (j (s0 + τ))] at this

end Shift

section Helpers
open LuoSunLiu.DIP

theorem revenue_eq_iSup (F : ℝ → ℝ) (hF : Continuous F) (q a : ℝ) (ha : 0 < a)
    (hmax : ∀ r : ℝ, 0 < r → revenue F q r ≤ revenue F q a) :
    revenue F q a = ⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue F q (r.1 : ℝ) := by
  have hbdd : BddAbove (Set.range fun r : {r : ℚ // (0 : ℝ) < r} => revenue F q (r.1 : ℝ)) :=
    ⟨revenue F q a, by rintro _ ⟨r, rfl⟩; exact hmax _ r.2⟩
  have : Nonempty {r : ℚ // (0 : ℝ) < r} := ⟨⟨1, by norm_num⟩⟩
  apply le_antisymm
  · have hc : Continuous (fun r => revenue F q r) := by
      unfold revenue; fun_prop
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hc a ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max (a - δ) (a / 2) < a by
      rcases max_cases (a - δ) (a / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> linarith)
    have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_right _ _) hr1)
    have hd : dist (r : ℝ) a < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [le_max_left (a - δ) (a / 2)]
    have := hball r hd
    rw [Real.dist_eq, abs_lt] at this
    have hle : revenue F q (r : ℝ) ≤ ⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue F q (r.1 : ℝ) :=
      le_ciSup hbdd ⟨r, hr0⟩
    linarith [this.1]
  · exact ciSup_le fun r => hmax _ r.2

theorem perRegret_measurable {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) {Ω : Type*} [MeasurableSpace Ω] (x : Ω → Fin d0 → ℝ)
    (q : Ω → ℝ) (hx : Measurable x) (hq : Measurable q) (hX : ∀ ω, x ω ∈ M.X) :
    Measurable fun ω => perRegret M (x ω) (q ω) := by
  have hFc : Continuous M.F := hL.continuous
  have hrev : Continuous (fun v : ℝ × ℝ => revenue M.F v.1 v.2) := by
    unfold revenue; fun_prop
  have heq : (fun ω => perRegret M (x ω) (q ω)) = fun ω =>
      (⨆ r : {r : ℚ // (0 : ℝ) < r}, revenue M.F (x ω ⬝ᵥ M.θ0) (r.1 : ℝ)) -
        revenue M.F (x ω ⬝ᵥ M.θ0) (q ω) := by
    funext ω
    obtain ⟨-, -, -, hst⟩ := hM
    obtain ⟨⟨hs0, -⟩, hmax⟩ := hst (x ω) (hX ω)
    unfold perRegret
    rw [revenue_eq_iSup M.F hFc _ _ hs0 hmax]
  rw [heq]
  have hdot : Measurable fun ω => x ω ⬝ᵥ M.θ0 := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hx).mul_const _
  refine Measurable.sub ?_ ?_
  · refine Measurable.iSup fun r => ?_
    exact hrev.measurable.comp (hdot.prodMk measurable_const)
  · exact hrev.measurable.comp (hdot.prodMk hq)

theorem l1_continuous {d0 : ℕ} : Continuous (fun v : Fin d0 → ℝ => l1 v) := by
  unfold l1; fun_prop

/-- The data vector up to local time `t`. -/
def Yt {d0 : ℕ} {Ω : Type*} (θh : Ω → Fin d0 → ℝ) (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ)
    (s0 t : ℕ) (ω : Ω) :
    (Fin d0 → ℝ) × (Fin (t + 1) → Fin d0 → ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  (θh ω, fun s => x (s0 + s + 1) ω, fun s => p (s0 + s + 1) ω, fun s => z (s0 + s + 1) ω)

def restr {d0 t : ℕ}
    (v : (Fin d0 → ℝ) × (Fin (t + 1 + 1) → Fin d0 → ℝ) × (Fin (t + 1 + 1) → ℝ) × (Fin (t + 1) → ℝ)) :
    (Fin d0 → ℝ) × (Fin (t + 1) → Fin d0 → ℝ) × (Fin (t + 1) → ℝ) × (Fin t → ℝ) :=
  (v.1, fun s => v.2.1 s.castSucc, fun s => v.2.2.1 s.castSucc, fun s => v.2.2.2 s.castSucc)

theorem restr_measurable {d0 t : ℕ} : Measurable (restr (d0 := d0) (t := t)) := by
  unfold restr; fun_prop

theorem Yt_measurable {d0 : ℕ} {Ω : Type*} [mm : MeasurableSpace Ω] (θh : Ω → Fin d0 → ℝ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (s0 t : ℕ) (hθ : Measurable θh)
    (hx : ∀ s, s < t + 1 → Measurable (x (s0 + s + 1)))
    (hp : ∀ s, s < t + 1 → Measurable (p (s0 + s + 1)))
    (hz : ∀ s, s < t → Measurable (z (s0 + s + 1))) : Measurable (Yt θh x z p s0 t) := by
  unfold Yt
  refine hθ.prodMk ((measurable_pi_lambda _ fun s : Fin (t + 1) => hx s.1 s.2).prodMk
    ((measurable_pi_lambda _ fun s : Fin (t + 1) => hp s.1 s.2).prodMk
      (measurable_pi_lambda _ fun s : Fin t => hz s.1 s.2)))

/-- The natural filtration of the shifted data (together with the estimate). -/
def Nf {d0 : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (θh : Ω → Fin d0 → ℝ)
    (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ) (s0 : ℕ)
    (hY : ∀ t, Measurable (Yt θh x z p s0 t)) : Filtration ℕ mΩ where
  seq t := MeasurableSpace.comap (Yt θh x z p s0 t) inferInstance
  mono' := by
    refine monotone_nat_of_le_succ fun t => ?_
    have : Yt θh x z p s0 t = restr ∘ Yt θh x z p s0 (t + 1) := rfl
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono restr_measurable.comap_le
  le' t := (hY t).comap_le

theorem comp_comap_meas {Ω E F : Type*} [mE : MeasurableSpace E] [MeasurableSpace F]
    (Y : Ω → E) (g : E → F) (hg : Measurable g) :
    Measurable[MeasurableSpace.comap Y mE] (fun ω => g (Y ω)) :=
  hg.comp (comap_measurable Y)

theorem ite_meas {Ω F : Type*} [mm : MeasurableSpace Ω] [MeasurableSpace F] {d0 : ℕ}
    (θ : Ω → Fin d0 → ℝ) (v : Fin d0 → ℝ) [∀ ω, Decidable (θ ω = v)]
    (hG : MeasurableSet {ω | θ ω = v}) (f : Ω → F) (hf : Measurable f) (c : F) :
    Measurable (fun ω => if θ ω = v then f ω else c) :=
  Measurable.ite hG hf measurable_const

theorem indep_congr_left {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    {Z Z' : Ω → ℝ} (h : Z' =ᵐ[μ] Z) (m2 : MeasurableSpace Ω)
    (hI : Indep (MeasurableSpace.comap Z inferInstance) m2 μ) :
    Indep (MeasurableSpace.comap Z' inferInstance) m2 μ := by
  rw [Indep_iff] at hI ⊢
  rintro t1 t2 ⟨U, hU, rfl⟩ ht2
  have hset : (Z' ⁻¹' U : Set Ω) =ᵐ[μ] (Z ⁻¹' U : Set Ω) :=
    h.mono fun ω hω => by
      show (Z' ω ∈ U) = (Z ω ∈ U)
      rw [hω]
  rw [measure_congr (hset.inter (ae_eq_refl t2)), measure_congr hset]
  exact hI _ _ ⟨U, hU, rfl⟩ ht2

end Helpers

end LuoSunLiu.DIP.P3CondAux

open LuoSunLiu.DIP LuoSunLiu.DIP.P3CondAux in
theorem solution {d0 : ℕ} (M : PricingModel d0) (hM : M.Standing) (L : ℝ≥0)
    (hL : LipschitzWith L M.F) (CA : ℝ) (hA2 : Assumption2 M CA)
    (Cdisc : ℕ) (hCdisc : M.pmax + 2 * M.W < Cdisc * M.pmax) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C2' C3' : ℝ, 0 < C2' ∧ 0 < C3' ∧
      ∀ (Ω : Type*) (mΩ : MeasurableSpace Ω) [StandardBorelSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Filtration ℕ mΩ)
        (x : ℕ → Ω → Fin d0 → ℝ) (z p : ℕ → Ω → ℝ), IsPricingEnv M P 𝒢 x z p →
      ∀ (s0 T0 : ℕ), 1 ≤ T0 →
      ∀ (θh : Ω → Fin d0 → ℝ), Measurable[𝒢 s0] θh → (∀ ω, l1 (θh ω) ≤ M.W) →
      (∀ ω, ∃ j : ℕ → Fin (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊),
        IsInnerBRun M.pmax (θh ω) lam
          (betaStar M.pmax lam (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊) (1 / (T0 : ℝ))) s0 T0
          (fun t => x t ω) j (fun t => p t ω) (fun t => response M x z p t ω)) →
      ∫⁻ ω, ENNReal.ofReal (∑ t ∈ Finset.Icc (s0 + 1) (s0 + T0), perRegret M (x t ω) (p t ω)) ∂P ≤
        ENNReal.ofReal (C3' * Real.log (C2' * T0) * (T0 : ℝ) ^ ((2 : ℝ) / 3)) +
          ENNReal.ofReal (4 * M.pmax * L * T0) *
            ∫⁻ ω, ENNReal.ofReal (l1 (θh ω - M.θ0)) ∂P := by
  obtain ⟨C2, C3, hC2, hC3, h3⟩ := (proposition_3.{0, _} M hM L hL CA hA2).2 Cdisc hCdisc lam hlam
  refine ⟨C2, C3, hC2, hC3, ?_⟩
  intro Ω mΩ _ P _ 𝒢 x z p hEnv s0 T0 hT0 θh hθ hW hrun
  classical
  have hm : 𝒢 s0 ≤ mΩ := 𝒢.le s0
  -- measurability facts
  have hxG : ∀ t, 1 ≤ t → ∀ u, t - 1 ≤ u → Measurable[𝒢 u] (x t) := fun t ht u hu =>
    (hEnv t ht).1.mono (𝒢.mono hu) le_rfl
  have hpG : ∀ t, 1 ≤ t → ∀ u, t - 1 ≤ u → Measurable[𝒢 u] (p t) := fun t ht u hu =>
    (hEnv t ht).2.1.mono (𝒢.mono hu) le_rfl
  have hzG : ∀ t, 1 ≤ t → ∀ u, t ≤ u → Measurable[𝒢 u] (z t) := fun t ht u hu =>
    (hEnv t ht).2.2.1.mono (𝒢.mono hu) le_rfl
  have hYG : ∀ u, Measurable[𝒢 (s0 + u)] (Yt θh x z p s0 u) := fun u =>
    Yt_measurable (mm := 𝒢 (s0 + u)) θh x z p s0 u (hθ.mono (𝒢.mono (by omega)) le_rfl)
      (fun s hs => hxG _ (by omega) _ (by omega)) (fun s hs => hpG _ (by omega) _ (by omega))
      (fun s hs => hzG _ (by omega) _ (by omega))
  have hY : ∀ u, Measurable (Yt θh x z p s0 u) := fun u => (hYG u).mono (𝒢.le _) le_rfl
  set N := Nf θh x z p s0 hY with hN
  have hzm : ∀ t, 1 ≤ t → Measurable (z t) := fun t ht => (hEnv t ht).2.2.1.mono (𝒢.le _) le_rfl
  have hxm : ∀ t, 1 ≤ t → Measurable (x t) := fun t ht => (hEnv t ht).1.mono (𝒢.le _) le_rfl
  have hpm : ∀ t, 1 ≤ t → Measurable (p t) := fun t ht => (hEnv t ht).2.1.mono (𝒢.le _) le_rfl
  -- a.e. facts
  have hci : ∀ᵐ a ∂(P.trim hm), ∀ u : ℕ,
      Indep (MeasurableSpace.comap (z (s0 + u + 1)) inferInstance)
        (MeasurableSpace.comap (Yt θh x z p s0 u) inferInstance) (condExpKernel P (𝒢 s0) a) ∧
      ∀ c : ℝ, (condExpKernel P (𝒢 s0) a).real {ω | z (s0 + u + 1) ω ≤ c} =
        P.real {ω | z (s0 + u + 1) ω ≤ c} := by
    refine ae_all_iff.2 fun u => ci_ae hm (z (s0 + u + 1)) (hzm _ (by omega))
      (Yt θh x z p s0 u) (hY u) ?_
    have hI := (hEnv (s0 + u + 1) (by omega)).2.2.2.2.2
    refine indep_of_indep_of_le_right hI ?_
    exact sup_le ((hYG u).comap_le.trans (𝒢.mono (by omega))) (𝒢.mono (by omega))
  have hfib := fiber_null (P := P) hm θh hθ
  set A : ℝ := C3 * Real.log (C2 * T0) * (T0 : ℝ) ^ ((2 : ℝ) / 3) with hA
  set B : ℝ := 4 * M.pmax * L * T0 with hB
  have hB0 : 0 ≤ B := by have := hM.2.1.le; positivity
  set R : Ω → ℝ := fun ω => ∑ t ∈ Finset.Icc (s0 + 1) (s0 + T0), perRegret M (x t ω) (p t ω)
    with hR
  have hRm : Measurable R := Finset.measurable_sum _ fun t ht => by
    rw [Finset.mem_Icc] at ht
    exact perRegret_measurable M hM L hL (x t) (p t) (hxm t (by omega)) (hpm t (by omega))
      (hEnv t (by omega)).2.2.2.1
  have hbound : ∀ᵐ a ∂(P.trim hm), ∫⁻ ω, ENNReal.ofReal (R ω) ∂(condExpKernel P (𝒢 s0) a) ≤
      ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (l1 (θh a - M.θ0)) := by
    filter_upwards [hci, hfib] with a hca hfa
    have hgood : ∀ᵐ ω ∂(condExpKernel P (𝒢 s0) a), θh ω = θh a := ae_iff.2 hfa
    let x' : ℕ → Ω → Fin d0 → ℝ := fun t ω => if θh ω = θh a then x (s0 + t) ω else x (s0 + t) a
    let z' : ℕ → Ω → ℝ := fun t ω => if θh ω = θh a then z (s0 + t) ω else z (s0 + t) a
    let p' : ℕ → Ω → ℝ := fun t ω => if θh ω = θh a then p (s0 + t) ω else p (s0 + t) a
    have hG : ∀ u, MeasurableSet[N u] {ω | θh ω = θh a} := fun u =>
      comp_comap_meas (Yt θh x z p s0 u) (fun v => v.1) measurable_fst
        (measurableSet_singleton (θh a))
    have hzae : ∀ u : ℕ, z' (u + 1) =ᵐ[condExpKernel P (𝒢 s0) a] z (s0 + u + 1) := fun u =>
      hgood.mono fun ω h => by simp only [z', if_pos h]; rfl
    have henv : IsPricingEnv M (condExpKernel P (𝒢 s0) a) N x' z' p' := by
      intro t ht
      obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ite_meas (mm := N u) θh (θh a) (hG u) _
          (comp_comap_meas (Yt θh x z p s0 u) (fun v => v.2.1 (Fin.last u)) (by fun_prop)) _
      · exact ite_meas (mm := N u) θh (θh a) (hG u) _
          (comp_comap_meas (Yt θh x z p s0 u) (fun v => v.2.2.1 (Fin.last u)) (by fun_prop)) _
      · exact ite_meas (mm := N (u + 1)) θh (θh a) (hG (u + 1)) _
          (comp_comap_meas (Yt θh x z p s0 (u + 1)) (fun v => v.2.2.2 (Fin.last u))
            (by fun_prop)) _
      · intro ω
        simp only [x']
        split_ifs
        · exact (hEnv (s0 + (u + 1)) (by omega)).2.2.2.1 ω
        · exact (hEnv (s0 + (u + 1)) (by omega)).2.2.2.1 a
      · intro c
        have hset : {ω | z' (u + 1) ω ≤ c} =ᵐ[condExpKernel P (𝒢 s0) a]
            {ω | z (s0 + u + 1) ω ≤ c} :=
          (hzae u).mono fun ω h => by
            show (z' (u + 1) ω ≤ c) = (z (s0 + u + 1) ω ≤ c)
            rw [h]
        rw [measureReal_congr hset, (hca u).2 c]
        exact (hEnv (s0 + u + 1) (by omega)).2.2.2.2.1 c
      · exact indep_congr_left _ (hzae u) _ (hca u).1
    have hrun' : ∀ ω, ∃ j : ℕ → Fin (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊),
        IsInnerBRun M.pmax (θh a) lam
          (betaStar M.pmax lam (Cdisc * ⌈(T0 : ℝ) ^ ((1 : ℝ) / 6)⌉₊) (1 / (T0 : ℝ))) 0 T0
          (fun t => x' t ω) j (fun t => p' t ω) (fun t => response M x' z' p' t ω) := by
      intro ω
      by_cases hω : θh ω = θh a
      · obtain ⟨j, hj⟩ := hrun ω
        refine ⟨fun t => j (s0 + t), ?_⟩
        have := innerB_shift _ _ _ _ s0 T0 _ j _ _ hj
        rw [hω] at this
        have e1 : (fun t => x' t ω) = fun t => x (s0 + t) ω := funext fun t => if_pos hω
        have e2 : (fun t => p' t ω) = fun t => p (s0 + t) ω := funext fun t => if_pos hω
        have e3 : (fun t => response M x' z' p' t ω) = fun t => response M x z p (s0 + t) ω :=
          funext fun t => by simp only [response, x', z', p', if_pos hω]
        rw [e1, e2, e3]; exact this
      · obtain ⟨j, hj⟩ := hrun a
        refine ⟨fun t => j (s0 + t), ?_⟩
        have := innerB_shift _ _ _ _ s0 T0 _ j _ _ hj
        have e1 : (fun t => x' t ω) = fun t => x (s0 + t) a := funext fun t => if_neg hω
        have e2 : (fun t => p' t ω) = fun t => p (s0 + t) a := funext fun t => if_neg hω
        have e3 : (fun t => response M x' z' p' t ω) = fun t => response M x z p (s0 + t) a :=
          funext fun t => by simp only [response, x', z', p', if_neg hω]
        rw [e1, e2, e3]; exact this
    have hP3 := h3 (θh a) (hW a) Ω mΩ (condExpKernel P (𝒢 s0) a) N x' z' p' henv T0 hT0 hrun'
    have hcongr : ∫⁻ ω, ENNReal.ofReal (R ω) ∂(condExpKernel P (𝒢 s0) a) =
        ∫⁻ ω, ENNReal.ofReal (cumRegret M x' p' T0 ω) ∂(condExpKernel P (𝒢 s0) a) := by
      refine lintegral_congr_ae (hgood.mono fun ω h => ?_)
      simp only [hR, cumRegret]
      rw [← Finset.map_add_left_Icc 1 T0 s0, Finset.sum_map]
      simp only [addLeftEmbedding_apply, x', p', if_pos h]
    rw [hcongr]
    refine hP3.trans ?_
    refine (ENNReal.ofReal_add_le).trans ?_
    rw [← ENNReal.ofReal_mul hB0]
    have hq : 4 * M.pmax * (L : ℝ) * l1 (θh a - M.θ0) * T0 = B * l1 (θh a - M.θ0) := by
      rw [hB]; ring
    rw [hq]
  -- integrate
  have hgm : Measurable[𝒢 s0] (fun a => ENNReal.ofReal (l1 (θh a - M.θ0))) :=
    ENNReal.measurable_ofReal.comp (l1_continuous.measurable.comp (hθ.sub_const _))
  calc ∫⁻ ω, ENNReal.ofReal (R ω) ∂P
      = ∫⁻ ω, ENNReal.ofReal (R ω) ∂(condExpKernel P (𝒢 s0) ∘ₘ P.trim hm) := by
        rw [condExpKernel_comp_trim hm]
    _ = ∫⁻ a, ∫⁻ ω, ENNReal.ofReal (R ω) ∂(condExpKernel P (𝒢 s0) a) ∂(P.trim hm) :=
        Measure.lintegral_bind (condExpKernel P (𝒢 s0)).measurable.aemeasurable
          hRm.ennreal_ofReal.aemeasurable
    _ ≤ ∫⁻ a, (ENNReal.ofReal A + ENNReal.ofReal B * ENNReal.ofReal (l1 (θh a - M.θ0)))
          ∂(P.trim hm) := lintegral_mono_ae hbound
    _ = ENNReal.ofReal A + ENNReal.ofReal B *
          ∫⁻ a, ENNReal.ofReal (l1 (θh a - M.θ0)) ∂(P.trim hm) := by
        rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hgm,
          trim_measurableSet_eq hm MeasurableSet.univ, measure_univ, mul_one]
    _ = _ := by rw [lintegral_trim hm hgm]
