-- Prove2me | solution 1 for NashFlowLT.SteadyState.queue_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:43:43.597212+00:00
-- url     : https://prove2.me/submissions/37410238-86f8-49bd-a4af-d65da5e5fd00

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

open NashFlowLT.SteadyState MeasureTheory Set Finset Filter Topology

namespace P2MNFLTQ

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma queueRate_abs_le (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (e : E) (x : ℝ) :
    |queueRate N F e x| ≤ |F.fin e x| + N.nu e := by
  have hnu := hN.1 e
  unfold queueRate
  split_ifs
  · calc |F.fin e x - N.nu e| ≤ |F.fin e x| + |N.nu e| := abs_sub _ _
      _ = |F.fin e x| + N.nu e := by rw [abs_of_pos hnu]
  · rcases le_total (F.fin e x - N.nu e) 0 with h | h
    · rw [max_eq_right h, abs_zero]; positivity
    · rw [max_eq_left h]
      calc |F.fin e x - N.nu e| ≤ |F.fin e x| + |N.nu e| := abs_sub _ _
        _ = |F.fin e x| + N.nu e := by rw [abs_of_pos hnu]

lemma queueRate_ge (N : Network V E) (F : FlowOverTime V E) (hF : IsFlowOverTime N F)
    (e : E) (x : ℝ) (hx : 0 ≤ x) : -N.nu e ≤ queueRate N F e x := by
  have := hF.2.1 e x hx
  unfold queueRate
  split_ifs
  · linarith
  · exact le_trans (by linarith) (le_max_left _ _)

lemma qInt (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (hF : IsFlowOverTime N F)
    (e : E) : ∀ T, 0 ≤ T → IntervalIntegrable (queueRate N F e) volume 0 T := by
  set q := queueRate N F e with hqdef
  -- integrability on `Ioc 0 T` follows from a.e.-strong measurability there
  have hdom : ∀ T, 0 ≤ T → AEStronglyMeasurable q (volume.restrict (Ioc 0 T)) →
      IntervalIntegrable q volume 0 T := by
    intro T hT hm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hfi : IntegrableOn (fun x => |F.fin e x| + N.nu e) (Ioc 0 T) := by
      have h1 := (hF.2.2.1 e T).mono_set Ioc_subset_Icc_self
      exact (h1.abs).add (integrableOn_const (by simp [Real.volume_Ioc]))
    refine hfi.mono' hm ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa [Real.norm_eq_abs] using queueRate_abs_le N hN F e x)
  by_contra hcon
  push_neg at hcon
  set A := {T : ℝ | 0 ≤ T ∧ ¬ IntervalIntegrable q volume 0 T} with hA
  have hAne : A.Nonempty := by
    obtain ⟨T, hT, hT'⟩ := hcon; exact ⟨T, hT, hT'⟩
  have hAbdd : BddBelow A := ⟨0, fun x hx => hx.1⟩
  set T0 := sInf A with hT0
  have hT0nn : 0 ≤ T0 := le_csInf hAne (fun x hx => hx.1)
  have hbelow : ∀ x, 0 ≤ x → x < T0 → IntervalIntegrable q volume 0 x := by
    intro x hx hxT
    by_contra h
    exact absurd (csInf_le hAbdd ⟨hx, h⟩) (not_le.2 hxT)
  have habove : ∀ x, T0 < x → F.z e x = 0 := by
    intro x hx
    obtain ⟨T, ⟨hT0', hTn⟩, hTx⟩ := exists_lt_of_csInf_lt hAne hx
    have hxz : F.z e x = ∫ t in (0:ℝ)..x, queueRate N F e t := (hF.2.2.2.1 e x (by linarith)).2
    rw [hxz]
    apply intervalIntegral.integral_undef
    intro hint
    apply hTn
    exact hint.mono_set (uIcc_subset_uIcc_left (by simp [uIcc_of_le (by linarith : (0:ℝ) ≤ x)]; constructor <;> linarith))
  -- measurability on `Ioi 0`
  have hmeas : AEStronglyMeasurable q (volume.restrict (Ioi 0)) := by
    have hsub : Ioi (0:ℝ) ⊆ (⋃ n : ℕ, Ioc 0 (T0 - 1 / ((n:ℝ) + 1))) ∪ ({T0} ∪ Ioi T0) := by
      intro x hx
      rcases lt_trichotomy x T0 with h | h | h
      · left
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
        refine mem_iUnion.2 ⟨n, hx, ?_⟩
        linarith
      · right; left; exact h
      · right; right; exact h
    refine AEStronglyMeasurable.mono_set hsub ?_
    rw [aestronglyMeasurable_union_iff, aestronglyMeasurable_union_iff, aestronglyMeasurable_iUnion_iff]
    refine ⟨fun n => ?_, ?_, ?_⟩
    · set c := T0 - 1 / ((n:ℝ) + 1)
      rcases lt_or_ge c 0 with hc | hc
      · rw [Set.Ioc_eq_empty (by linarith), Measure.restrict_empty]
        exact aestronglyMeasurable_zero_measure _
      · have hcT : c < T0 := by
          have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
          linarith
        have := hbelow c hc hcT
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc] at this
        exact this.aestronglyMeasurable
    · have : volume.restrict ({T0} : Set ℝ) = 0 := Measure.restrict_eq_zero.2 (Real.volume_singleton)
      rw [this]; exact aestronglyMeasurable_zero_measure _
    · have hb : AEStronglyMeasurable (fun x => max (F.fin e x - N.nu e) 0) (volume.restrict (Ioi T0)) :=
        (((hF.1 e).sub measurable_const).max measurable_const).aestronglyMeasurable
      refine hb.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [q, queueRate, habove x hx, lt_irrefl, if_false]
  obtain ⟨T, hT, hTn⟩ := hcon
  apply hTn
  apply hdom T hT
  exact hmeas.mono_set Ioc_subset_Ioi_self

lemma pathTime_append (N : Network V E) (F : FlowOverTime V E) (p q : List E) (x : ℝ) :
    pathTime N F (p ++ q) x = pathTime N F q (pathTime N F p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append, pathTime]; exact ih _

lemma exitTime_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (x : ℝ) (hx : 0 ≤ x) : x ≤ exitTime N F e x := by
  have hz := (hF.2.2.2.1 e x hx).1
  have hnu := hN.1 e
  have htau := hN.2.1 e
  unfold exitTime
  have : 0 ≤ F.z e x / N.nu e := div_nonneg hz hnu.le
  linarith

lemma pathTime_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (p : List E) (x : ℝ) (hx : 0 ≤ x) : x ≤ pathTime N F p x := by
  induction p generalizing x with
  | nil => exact le_rfl
  | cons e p ih =>
    simp only [pathTime]
    have h1 := exitTime_ge N hN F hF e x hx
    exact h1.trans (ih _ (hx.trans h1))

lemma walkNodes_length (N : Network V E) (v : V) (p : List E) :
    (walkNodes N v p).length = p.length + 1 := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih => simp [walkNodes, ih]

lemma walkNodes_append_single (N : Network V E) (x : V) (p : List E) (e : E) :
    walkNodes N x (p ++ [e]) = walkNodes N x p ++ [N.head e] := by
  induction p generalizing x with
  | nil => rfl
  | cons e' p ih => simp [walkNodes, ih]

lemma isWalk_append_single (N : Network V E) (x v : V) (p : List E) (e : E)
    (hp : IsWalk N x v p) (he : N.tail e = v) : IsWalk N x (N.head e) (p ++ [e]) := by
  induction p generalizing x with
  | nil =>
    simp only [IsWalk] at hp
    subst hp
    simp [IsWalk, he]
  | cons e' p ih =>
    simp only [IsWalk] at hp
    simp only [List.cons_append, IsWalk]
    exact ⟨hp.1, ih _ hp.2⟩

lemma walkNodes_head (N : Network V E) (x : V) (p : List E) :
    ∃ l, walkNodes N x p = x :: l := by
  cases p with
  | nil => exact ⟨[], rfl⟩
  | cons e p => exact ⟨_, rfl⟩

lemma walkNodes_sublist (N : Network V E) (x : V) (p1 p2 : List E) :
    (walkNodes N x p1).Sublist (walkNodes N x (p1 ++ p2)) := by
  induction p1 generalizing x with
  | nil =>
    obtain ⟨l, hl⟩ := walkNodes_head N x p2
    simp only [walkNodes, List.nil_append, hl]
    exact List.Sublist.cons₂ _ (List.nil_sublist _)
  | cons e p ih =>
    simp only [walkNodes, List.cons_append]
    exact List.Sublist.cons₂ _ (ih _)

lemma path_prefix (N : Network V E) (p : List E) :
    ∀ a b : V, IsWalk N a b p → (walkNodes N a p).Nodup → ∀ w ∈ walkNodes N a p,
      ∃ p1 p2, p = p1 ++ p2 ∧ IsWalk N a w p1 ∧ (walkNodes N a p1).Nodup := by
  induction p with
  | nil =>
    intro a b _ _ w hw
    simp [walkNodes] at hw
    subst hw
    exact ⟨[], [], rfl, rfl, by simp [walkNodes]⟩
  | cons e p ih =>
    intro a b hwk hnd w hw
    simp only [IsWalk] at hwk
    simp only [walkNodes, List.mem_cons] at hw
    rcases hw with hw | hw
    · subst hw
      exact ⟨[], e :: p, rfl, rfl, by simp [walkNodes]⟩
    · simp only [walkNodes, List.nodup_cons] at hnd
      obtain ⟨p1, p2, hp, hw1, hnd1⟩ := ih _ _ hwk.2 hnd.2 w hw
      refine ⟨e :: p1, p2, by rw [hp]; rfl, ⟨hwk.1, hw1⟩, ?_⟩
      simp only [walkNodes, List.nodup_cons]
      refine ⟨fun hmem => hnd.1 ?_, hnd1⟩
      rw [hp]
      exact (walkNodes_sublist N _ p1 p2).subset hmem

lemma paths_finite (N : Network V E) (v : V) :
    {p : List E | IsPath N N.s v p}.Finite := by
  apply (List.finite_length_le E (Fintype.card V)).subset
  intro p hp
  have h1 := hp.2.length_le_card
  rw [walkNodes_length] at h1
  simp only [Set.mem_setOf_eq]
  omega

lemma ell_spec (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (v : V) (θ : ℝ) :
    (∃ p, IsPath N N.s v p ∧ ell N F v θ = pathTime N F p θ) ∧
      ∀ p, IsPath N N.s v p → ell N F v θ ≤ pathTime N F p θ := by
  set S := {r | ∃ p, IsPath N N.s v p ∧ r = pathTime N F p θ} with hS
  have hfin : S.Finite := by
    have : S = (fun p => pathTime N F p θ) '' {p : List E | IsPath N N.s v p} := by
      ext r; simp [S, eq_comm]
    rw [this]; exact (paths_finite N v).image _
  obtain ⟨p0, hp0⟩ := hN.2.2.2.2 v
  have hne : S.Nonempty := ⟨_, p0, hp0, rfl⟩
  refine ⟨?_, fun p hp => csInf_le hfin.bddBelow ⟨p, hp, rfl⟩⟩
  obtain ⟨p, hp, hr⟩ := hne.csInf_mem hfin
  exact ⟨p, hp, hr⟩

lemma ell_ge (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (v : V) (θ : ℝ) (hθ : 0 ≤ θ) : θ ≤ ell N F v θ := by
  obtain ⟨p, _, hp⟩ := (ell_spec N hN F v θ).1
  rw [hp]; exact pathTime_ge N hN F hF p θ hθ

lemma bellman (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (θ : ℝ) (hθ : 0 ≤ θ) :
    ell N F (N.head e) θ ≤ exitTime N F e (ell N F (N.tail e) θ) := by
  obtain ⟨p, hp, hpe⟩ := (ell_spec N hN F (N.tail e) θ).1
  have hpt0 : 0 ≤ pathTime N F p θ := hθ.trans (pathTime_ge N hN F hF p θ hθ)
  by_cases hw : N.head e ∈ walkNodes N N.s p
  · obtain ⟨p1, p2, hpp, hw1, hnd1⟩ := path_prefix N p N.s (N.tail e) hp.1 hp.2 _ hw
    have h1 := (ell_spec N hN F (N.head e) θ).2 p1 ⟨hw1, hnd1⟩
    have h2 : pathTime N F p1 θ ≤ pathTime N F p θ := by
      rw [hpp, pathTime_append]
      exact pathTime_ge N hN F hF p2 _ (hθ.trans (pathTime_ge N hN F hF p1 θ hθ))
    have h3 := exitTime_ge N hN F hF e (ell N F (N.tail e) θ) (by rw [hpe]; exact hpt0)
    rw [hpe] at h3 ⊢
    linarith
  · have hpath : IsPath N N.s (N.head e) (p ++ [e]) := by
      refine ⟨isWalk_append_single N _ _ p e hp.1 rfl, ?_⟩
      rw [walkNodes_append_single, List.nodup_append]
      refine ⟨hp.2, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      subst hb; subst hab; exact hw ha
    have h1 := (ell_spec N hN F (N.head e) θ).2 _ hpath
    rw [pathTime_append] at h1
    rw [hpe]
    simpa [pathTime] using h1


lemma z_sub (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (hF : IsFlowOverTime N F)
    (e : E) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    F.z e y - F.z e x = ∫ t in x..y, queueRate N F e t := by
  rw [(hF.2.2.2.1 e y (hx.trans hxy)).2, (hF.2.2.2.1 e x hx).2]
  exact intervalIntegral.integral_interval_sub_left (qInt N hN F hF e y (hx.trans hxy))
    (qInt N hN F hF e x hx)

lemma z_cont (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (hF : IsFlowOverTime N F)
    (e : E) (T : ℝ) (hT : 0 ≤ T) : ContinuousOn (F.z e) (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval' (qInt N hN F hF e T hT)
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  rw [uIcc_of_le hT] at h
  exact h.congr (fun x hx => (hF.2.2.2.1 e x hx.1).2)

lemma exitTime_mono (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    exitTime N F e x ≤ exitTime N F e y := by
  have hnu := hN.1 e
  have h1 := z_sub N hN F hF e x y hx hxy
  have h2 : ∫ t in x..y, (-N.nu e) ≤ ∫ t in x..y, queueRate N F e t := by
    apply intervalIntegral.integral_mono_on hxy (by simp) ((qInt N hN F hF e y (hx.trans hxy)).mono_set
      (Set.uIcc_subset_uIcc (by rw [uIcc_of_le (hx.trans hxy)]; exact ⟨hx, hxy⟩) right_mem_uIcc))
    intro t ht; exact queueRate_ge N F hF e t (hx.trans ht.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h2
  unfold exitTime
  have : F.z e y / N.nu e - F.z e x / N.nu e = (F.z e y - F.z e x) / N.nu e := by ring
  have h3 : -(y - x) ≤ (F.z e y - F.z e x) / N.nu e := by
    rw [le_div_iff₀ hnu]; nlinarith
  linarith

lemma exitTime_cont (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (exitTime N F e) (Icc 0 T) := by
  unfold exitTime
  exact ((continuousOn_id.add ((z_cont N hN F hF e T hT).div_const _)).add continuousOn_const)

lemma pathTime_mono (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (p : List E) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    pathTime N F p x ≤ pathTime N F p y := by
  induction p generalizing x y with
  | nil => exact hxy
  | cons e p ih =>
    simp only [pathTime]
    exact ih _ _ (hx.trans (exitTime_ge N hN F hF e x hx)) (exitTime_mono N hN F hF e x y hx hxy)

lemma ell_mono (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (v : V) : MonotoneOn (ell N F v) (Ici 0) := by
  intro x hx y _ hxy
  obtain ⟨p, hp, hpy⟩ := (ell_spec N hN F v y).1
  calc ell N F v x ≤ pathTime N F p x := (ell_spec N hN F v x).2 p hp
    _ ≤ pathTime N F p y := pathTime_mono N hN F hF p x y hx hxy
    _ = ell N F v y := hpy.symm

end P2MNFLTQ

open P2MNFLTQ in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    ∀ e θ, 0 ≤ θ → F.z e (ell N F (N.tail e) θ) =
      N.nu e * max (ell N F (N.head e) θ - ell N F (N.tail e) θ - N.tau e) 0 := by
  intro e θ hθ
  have hFO := hF.1
  set ξ := ell N F (N.tail e) θ with hξdef
  have hξ0 : 0 ≤ ξ := hθ.trans (ell_ge N hN F hFO _ θ hθ)
  have hnu := hN.1 e
  have hzξ := (hFO.2.2.2.1 e ξ hξ0).1
  have hbell := bellman N hN F hFO e θ hθ
  have key : 0 < F.z e ξ → exitTime N F e ξ ≤ ell N F (N.head e) θ := by
    intro hpos
    by_contra hlt
    push_neg at hlt
    set R := exitTime N F e ξ with hR
    set L := ell N F (N.head e) θ with hL
    -- the last time `ξ₀ ≤ ξ` at which the queue was empty
    set Z := {x : ℝ | x ∈ Icc 0 ξ ∧ F.z e x = 0} with hZ
    have hz00 : F.z e 0 = 0 := by rw [(hFO.2.2.2.1 e 0 le_rfl).2]; simp
    have hZne : (0:ℝ) ∈ Z := ⟨⟨le_rfl, hξ0⟩, hz00⟩
    have hZbdd : BddAbove Z := ⟨ξ, fun x hx => hx.1.2⟩
    have hZclosed : IsClosed Z := by
      have := (z_cont N hN F hFO e ξ hξ0).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_singleton (x := (0:ℝ)))
      have hZeq : Z = Icc 0 ξ ∩ F.z e ⁻¹' {0} := by ext x; simp [Z]
      rw [hZeq]; exact this
    set ξ0 := sSup Z with hξ0def
    have hξ0mem : ξ0 ∈ Z := hZclosed.csSup_mem ⟨0, hZne⟩ hZbdd
    have hξ0nn : 0 ≤ ξ0 := hξ0mem.1.1
    have hξ0lt : ξ0 < ξ := by
      rcases lt_or_eq_of_le hξ0mem.1.2 with h | h
      · exact h
      · exfalso; have := hξ0mem.2; rw [h] at this; linarith
    have hzpos : ∀ x, ξ0 < x → x ≤ ξ → 0 < F.z e x := by
      intro x h1 h2
      have hz0 := (hFO.2.2.2.1 e x (by linarith)).1
      rcases eq_or_lt_of_le hz0 with h | h
      · exfalso
        have hx : x ∈ Z := ⟨⟨by linarith, h2⟩, h.symm⟩
        linarith [le_csSup hZbdd hx]
      · exact h
    have hfinint : IntervalIntegrable (F.fin e) volume 0 ξ := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hξ0]; exact hFO.2.2.1 e ξ
    have hfsub : ∀ a b, 0 ≤ a → a ≤ b → b ≤ ξ → IntervalIntegrable (F.fin e) volume a b := by
      intro a b ha hab hb
      exact hfinint.mono_set (Set.uIcc_subset_uIcc (by rw [uIcc_of_le hξ0]; exact ⟨ha, hab.trans hb⟩)
        (by rw [uIcc_of_le hξ0]; exact ⟨ha.trans hab, hb⟩))
    -- exit-time increments on the queuing interval
    have hTdiff : ∀ y, ξ0 ≤ y → y ≤ ξ →
        R - exitTime N F e y = (∫ t in y..ξ, F.fin e t) / N.nu e := by
      intro y hy1 hy2
      have hy0 : 0 ≤ y := le_trans hξ0nn hy1
      have h1 := z_sub N hN F hFO e y ξ hy0 hy2
      have h2 : ∫ t in y..ξ, queueRate N F e t = ∫ t in y..ξ, (F.fin e t - N.nu e) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hy2] at ht
        simp only [queueRate, if_pos (hzpos t (by linarith [ht.1]) ht.2)]
      rw [h2, intervalIntegral.integral_sub (hfsub y ξ hy0 hy2 le_rfl) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul] at h1
      have h3 : F.z e ξ = F.z e y + ((∫ t in y..ξ, F.fin e t) - (ξ - y) * N.nu e) := by linarith
      simp only [hR, exitTime]
      rw [h3]
      field_simp
      ring
    set J : ℝ → ℝ := fun y => ∫ t in y..ξ, F.fin e t with hJ
    have hJnn : ∀ y, 0 ≤ y → y ≤ ξ → 0 ≤ J y := fun y hy hyξ =>
      intervalIntegral.integral_nonneg hyξ (fun t ht => hFO.2.1 e t (hy.trans ht.1))
    have hJcont : ContinuousOn J (Icc ξ0 ξ) := by
      have h := intervalIntegral.continuousOn_primitive_interval'
        (hfsub ξ0 ξ hξ0nn hξ0lt.le le_rfl) (right_mem_uIcc : ξ ∈ uIcc ξ0 ξ)
      rw [uIcc_of_le hξ0lt.le] at h
      refine h.neg.congr (fun y _ => ?_)
      simp only [J, Pi.neg_apply]
      rw [intervalIntegral.integral_symm]
    have hJξ0 : 0 < J ξ0 := by
      have h1 := hTdiff ξ0 le_rfl hξ0lt.le
      have h2 : R - exitTime N F e ξ0 = (ξ - ξ0) + F.z e ξ / N.nu e := by
        simp only [hR, exitTime, hξ0mem.2]; ring
      have h3 : 0 < (ξ - ξ0) + F.z e ξ / N.nu e := by
        have := div_pos hpos hnu; linarith
      rw [h2] at h1
      rw [h1] at h3
      exact (div_pos_iff_of_pos_right hnu).1 h3
    -- the last time `ys ≤ ξ` with positive inflow afterwards
    set Y := {y : ℝ | y ∈ Icc ξ0 ξ ∧ J y = 0} with hY
    have hξY : ξ ∈ Y := ⟨⟨hξ0lt.le, le_rfl⟩, by simp [J]⟩
    have hYbdd : BddBelow Y := ⟨ξ0, fun y hy => hy.1.1⟩
    have hYclosed : IsClosed Y := by
      have := hJcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0:ℝ)))
      have hYeq : Y = Icc ξ0 ξ ∩ J ⁻¹' {0} := by ext x; simp [Y]
      rw [hYeq]; exact this
    set ys := sInf Y with hysdef
    have hysmem : ys ∈ Y := hYclosed.csInf_mem ⟨ξ, hξY⟩ hYbdd
    have hysgt : ξ0 < ys := by
      rcases lt_or_eq_of_le hysmem.1.1 with h | h
      · exact h
      · exfalso; have := hysmem.2; rw [← h] at this; linarith
    have hysξ : ys ≤ ξ := hysmem.1.2
    have hTys : exitTime N F e ys = R := by
      have := hTdiff ys hysgt.le hysξ
      have h0 : J ys = 0 := hysmem.2
      simp only [J] at h0
      rw [h0, zero_div] at this
      linarith
    -- continuity of the exit time at `ys`
    have hcw := exitTime_cont N hN F hFO e ξ hξ0 ys ⟨by linarith, hysξ⟩
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨η, hη, hηprop⟩ := hcw (R - L) (by linarith)
    set a := max ξ0 (ys - η / 2) with ha
    have ha0 : 0 ≤ a := le_trans hξ0nn (le_max_left _ _)
    have has : a < ys := max_lt hysgt (by linarith)
    have hJa : 0 < J a := by
      rcases eq_or_lt_of_le (hJnn a ha0 (has.le.trans hysξ)) with h | h
      · exfalso
        have haY : a ∈ Y := ⟨⟨le_max_left _ _, has.le.trans hysξ⟩, h.symm⟩
        linarith [csInf_le hYbdd haY]
      · exact h
    have hint_pos : 0 < ∫ t in a..ys, F.fin e t := by
      have h1 : J a = (∫ t in a..ys, F.fin e t) + J ys := by
        simp only [J]
        rw [intervalIntegral.integral_add_adjacent_intervals (hfsub a ys ha0 has.le hysξ)
          (hfsub ys ξ (by linarith) hysξ le_rfl)]
      have h0 : J ys = 0 := hysmem.2
      linarith
    -- an inflow time in `(a, ys)` at which `e` is active
    have hex : ∃ x ∈ Ioo a ys, 0 < F.fin e x ∧
        x ∈ ell N F (N.tail e) '' {θ' | 0 ≤ θ' ∧ IsActive N F e θ'} := by
      by_contra hno
      push_neg at hno
      have h2 := ae_restrict_of_ae_restrict_of_subset
        (show Ioo a ys ⊆ Ici 0 from fun x hx => le_of_lt (lt_of_le_of_lt ha0 hx.1)) (hF.2 e)
      have h1 : ∀ᵐ x ∂(volume.restrict (Ioo a ys)), F.fin e x = 0 := by
        filter_upwards [h2, ae_restrict_mem measurableSet_Ioo] with x hx hxI
        by_contra hne
        have hfpos : 0 < F.fin e x :=
          lt_of_le_of_ne (hFO.2.1 e x (le_of_lt (lt_of_le_of_lt ha0 hxI.1))) (Ne.symm hne)
        exact hno x hxI hfpos (hx hfpos)
      have : ∫ t in a..ys, F.fin e t = 0 := by
        rw [intervalIntegral.integral_of_le has.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
        exact integral_eq_zero_of_ae h1
      linarith
    obtain ⟨x, hxI, _, θ', ⟨hθ'0, hact⟩, hθ'x⟩ := hex
    have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt ha0 hxI.1)
    have hθ'θ : θ' ≤ θ := by
      by_contra h
      push_neg at h
      have := ell_mono N hN F hFO (N.tail e) hθ hθ'0 h.le
      rw [hθ'x] at this
      linarith [hxI.2]
    have hmono := ell_mono N hN F hFO (N.head e) hθ'0 hθ hθ'θ
    have hact' : ell N F (N.head e) θ' = exitTime N F e x := by
      have := hact
      unfold IsActive at this
      rw [this, hθ'x]
    have hdist : dist x ys < η := by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have : ys - η / 2 ≤ a := le_max_right _ _
        linarith [hxI.1]
      · linarith [hxI.2]
    have hclose := hηprop ⟨hx0, (hxI.2.le.trans hysξ)⟩ hdist
    rw [hTys, Real.dist_eq, abs_lt] at hclose
    linarith [hclose.1]
  rcases eq_or_lt_of_le hzξ with h0 | hpos
  · rw [← h0]
    have hb := hbell
    rw [← hξdef] at hb
    simp only [exitTime, ← h0, zero_div, add_zero] at hb
    rw [max_eq_right (by linarith), mul_zero]
  · have hk := key hpos
    have heq : ell N F (N.head e) θ = exitTime N F e ξ := le_antisymm hbell hk
    rw [heq]
    simp only [exitTime]
    have h1 : ξ + F.z e ξ / N.nu e + N.tau e - ξ - N.tau e = F.z e ξ / N.nu e := by ring
    rw [h1, max_eq_left (div_nonneg hzξ hnu.le)]
    field_simp
