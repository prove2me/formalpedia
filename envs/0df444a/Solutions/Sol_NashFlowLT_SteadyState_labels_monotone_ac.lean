-- Prove2me | solution 1 for NashFlowLT.SteadyState.labels_monotone_ac
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:48:25.606528+00:00
-- url     : https://prove2.me/submissions/418c01ec-21ee-4a96-9576-3dc56df1cfd4

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

lemma ac_congr {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (h : ∀ x ∈ uIcc a b, f x = g x) : AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have := hδp E hE hlen
  convert this using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h _ (hE.1 i hi).1, h _ (hE.1 i hi).2]

lemma ac_abs {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => |f x|) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => lt_of_le_of_lt ?_ (hδp E hE hlen)⟩
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.dist_eq]
  exact abs_abs_sub_abs_le_abs_sub _ _

lemma ac_const (c a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  exact ⟨1, one_pos, fun E _ _ => by simpa using hε⟩

lemma ac_id (a b : ℝ) : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  exact ⟨ε, hε, fun E _ h => h⟩

lemma ac_min {f g : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => min (f x) (g x)) a b := by
  have h := ((hf.add hg).sub (ac_abs (hf.sub hg))).const_mul (1/2)
  refine ac_congr h (fun x _ => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  rcases le_total (f x) (g x) with hle | hle
  · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring

lemma monotoneOn_max_eq {g : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : g (max x y) = max (g x) (g y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, max_eq_right (hg hx hy h)]
  · rw [max_eq_left h, max_eq_left (hg hy hx h)]

lemma monotoneOn_min_eq {g : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) : g (min x y) = min (g x) (g y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, min_eq_left (hg hx hy h)]
  · rw [min_eq_right h, min_eq_right (hg hy hx h)]

lemma uIoc_image_disjoint {g : ℝ → ℝ} {s : Set ℝ} (hg : MonotoneOn g s) {x1 y1 x2 y2 : ℝ}
    (hx1 : x1 ∈ s) (hy1 : y1 ∈ s) (hx2 : x2 ∈ s) (hy2 : y2 ∈ s)
    (hd : Disjoint (uIoc x1 y1) (uIoc x2 y2)) :
    Disjoint (uIoc (g x1) (g y1)) (uIoc (g x2) (g y2)) := by
  simp only [uIoc] at hd ⊢
  rw [Set.Ioc_disjoint_Ioc] at hd ⊢
  have mem_max : ∀ {x y : ℝ}, x ∈ s → y ∈ s → max x y ∈ s := fun {x y} hx hy => by
    rcases max_choice x y with h | h <;> rw [h] <;> assumption
  have mem_min : ∀ {x y : ℝ}, x ∈ s → y ∈ s → min x y ∈ s := fun {x y} hx hy => by
    rcases min_choice x y with h | h <;> rw [h] <;> assumption
  rw [← monotoneOn_max_eq hg hx1 hy1, ← monotoneOn_max_eq hg hx2 hy2,
    ← monotoneOn_min_eq hg hx1 hy1, ← monotoneOn_min_eq hg hx2 hy2,
    ← monotoneOn_min_eq hg (mem_max hx1 hy1) (mem_max hx2 hy2),
    ← monotoneOn_max_eq hg (mem_min hx1 hy1) (mem_min hx2 hy2)]
  exact hg (mem_min (mem_max hx1 hy1) (mem_max hx2 hy2)) (mem_max (mem_min hx1 hy1) (mem_min hx2 hy2)) hd

lemma ac_comp {f g : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hf : AbsolutelyContinuousOnInterval f c d) (hg : AbsolutelyContinuousOnInterval g a b)
    (hgm : MonotoneOn g (Icc a b)) (hmaps : ∀ x ∈ Icc a b, g x ∈ Icc c d) :
    AbsolutelyContinuousOnInterval (fun x => f (g x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf hg ⊢
  intro ε hε
  obtain ⟨δf, hδf, hf'⟩ := hf ε hε
  obtain ⟨δg, hδg, hg'⟩ := hg δf hδf
  refine ⟨δg, hδg, fun E hE hlen => ?_⟩
  have hE1 : ∀ i ∈ Finset.range E.1, (E.2 i).1 ∈ Icc a b ∧ (E.2 i).2 ∈ Icc a b := by
    intro i hi; have := hE.1 i hi; rwa [uIcc_of_le hab] at this
  let E' : ℕ × (ℕ → ℝ × ℝ) := (E.1, fun i => (g (E.2 i).1, g (E.2 i).2))
  have hE' : E' ∈ AbsolutelyContinuousOnInterval.disjWithin c d := by
    refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
    · rw [uIcc_of_le hcd]; exact ⟨hmaps _ (hE1 i hi).1, hmaps _ (hE1 i hi).2⟩
    · have hd := hE.2 hi hj hij
      have hi' : i ∈ Finset.range E.1 := hi
      have hj' : j ∈ Finset.range E.1 := hj
      exact uIoc_image_disjoint hgm (hE1 i hi').1 (hE1 i hi').2 (hE1 j hj').1 (hE1 j hj').2 hd
  exact hf' E' hE' (hg' E hE hlen)

lemma z_ac (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E) (hF : IsFlowOverTime N F)
    (e : E) (T : ℝ) (hT : 0 ≤ T) : AbsolutelyContinuousOnInterval (F.z e) 0 T := by
  have h := (qInt N hN F hF e T hT).absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  refine ac_congr h (fun x hx => ?_)
  rw [uIcc_of_le hT] at hx
  exact (hF.2.2.2.1 e x hx.1).2.symm

lemma exitTime_ac (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (e : E) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (exitTime N F e) 0 T := by
  have h := ((ac_id 0 T).add ((z_ac N hN F hF e T hT).const_mul (1 / N.nu e))).add
    (ac_const (N.tau e) 0 T)
  refine ac_congr h (fun x _ => ?_)
  simp only [Pi.add_apply, exitTime]
  ring

lemma pathTime_ac (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (p : List E) :
    ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval (pathTime N F p) 0 T := by
  induction p with
  | nil => intro T _; exact ac_congr (ac_id 0 T) (fun x _ => rfl)
  | cons e p ih =>
    intro T hT
    have hTe : 0 ≤ exitTime N F e T := hT.trans (exitTime_ge N hN F hF e T hT)
    have h := ac_comp hT hTe (ih _ hTe) (exitTime_ac N hN F hF e T hT)
      (fun x hx y hy hxy => exitTime_mono N hN F hF e x y hx.1 hxy)
      (fun x hx => ⟨hx.1.trans (exitTime_ge N hN F hF e x hx.1),
        exitTime_mono N hN F hF e x T hx.1 hx.2⟩)
    exact ac_congr h (fun x _ => rfl)

lemma ac_inf' (N : Network V E) (F : FlowOverTime V E) (T : ℝ) (s : Finset (List E))
    (hs : s.Nonempty) (h : ∀ p ∈ s, AbsolutelyContinuousOnInterval (pathTime N F p) 0 T) :
    AbsolutelyContinuousOnInterval (fun θ => s.inf' hs (fun p => pathTime N F p θ)) 0 T := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.inf'_singleton]
    exact h a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    have h1 := h a (Finset.mem_cons_self a s)
    have h2 := ih (fun p hp => h p (Finset.mem_cons_of_mem hp))
    refine ac_congr (ac_min h1 h2) (fun x _ => ?_)
    rw [Finset.inf'_cons hs]

lemma ell_ac (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsFlowOverTime N F) (v : V) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (ell N F v) 0 T := by
  set P := (paths_finite N v).toFinset with hP
  obtain ⟨p0, hp0⟩ := hN.2.2.2.2 v
  have hne : P.Nonempty := ⟨p0, (paths_finite N v).mem_toFinset.2 hp0⟩
  have h := ac_inf' N F T P hne (fun p _ => pathTime_ac N hN F hF p T hT)
  refine ac_congr h (fun θ _ => ?_)
  apply le_antisymm
  · obtain ⟨p, hp, hpe⟩ := (ell_spec N hN F v θ).1
    rw [hpe]
    exact Finset.inf'_le (fun p => pathTime N F p θ) ((paths_finite N v).mem_toFinset.2 hp)
  · apply Finset.le_inf'
    intro p hp
    exact (ell_spec N hN F v θ).2 p ((paths_finite N v).mem_toFinset.1 hp)

end P2MNFLTQ

open P2MNFLTQ in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    (∀ v, MonotoneOn (ell N F v) (Ici 0) ∧
        ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval (ell N F v) 0 T) ∧
      (∀ e, MonotoneOn (staticFlow N F e) (Ici 0) ∧
        ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval (staticFlow N F e) 0 T) := by
  have hFO := hF.1
  refine ⟨fun v => ⟨ell_mono N hN F hFO v, fun T hT => ell_ac N hN F hFO v T hT⟩, fun e => ⟨?_, ?_⟩⟩
  · intro x hx y hy hxy
    have hx0 : (0:ℝ) ≤ x := hx
    have hlx : 0 ≤ ell N F (N.tail e) x := hx0.trans (ell_ge N hN F hFO _ x hx0)
    have hlxy : ell N F (N.tail e) x ≤ ell N F (N.tail e) y := ell_mono N hN F hFO _ hx hy hxy
    have hfi : IntervalIntegrable (F.fin e) volume 0 (ell N F (N.tail e) y) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (hlx.trans hlxy)]
      exact hFO.2.2.1 e _
    unfold staticFlow
    apply intervalIntegral.integral_mono_interval le_rfl hlx hlxy _ hfi
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hFO.2.1 e t (le_of_lt ht.1)
  · intro T hT
    set D := ell N F (N.tail e) T
    have hD : 0 ≤ D := hT.trans (ell_ge N hN F hFO _ T hT)
    have hfi : IntervalIntegrable (F.fin e) volume 0 D := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hD]
      exact hFO.2.2.1 e _
    have hF' := hfi.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 D)
    have h := ac_comp hT hD hF' (ell_ac N hN F hFO (N.tail e) T hT)
      ((ell_mono N hN F hFO (N.tail e)).mono (fun x hx => hx.1))
      (fun x hx => ⟨hx.1.trans (ell_ge N hN F hFO _ x hx.1),
        ell_mono N hN F hFO _ hx.1 hT hx.2⟩)
    exact ac_congr h (fun x _ => rfl)
