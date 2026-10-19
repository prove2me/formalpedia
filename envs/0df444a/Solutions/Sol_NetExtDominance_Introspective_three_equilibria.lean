-- Prove2me | solution 1 for NetExtDominance.Introspective.three_equilibria
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:55:40.486698+00:00
-- url     : https://prove2.me/submissions/b5cde943-5829-48e4-b89c-59dd3c376e14

import Mathlib
import Definitions.Def_NetExtDominance_Introspective_Setting
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Filter Topology
namespace NetworkResearch
open NetExtDominance.Introspective
lemma demand_cont (M : Market) (p : ℝ) : ContinuousOn (M.D p) (Set.Icc (0:ℝ) 1) := by
  exact M.hDcont.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx => ⟨Set.mem_univ _,hx⟩)
lemma iterate_mem (M : Market) (p x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) (n : ℕ) :
    (M.D p)^[n] x∈Set.Icc (0:ℝ) 1 := by
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [Function.iterate_succ_apply',Set.mem_Icc] using M.hD01 p _ ih
lemma iterate_limit (M : Market) (p x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) :
    ∃ q,IsEquilibriumQty M p q ∧ IsIntrospectiveEq M p x q := by
  let u : ℕ → ℝ := fun n => (M.D p)^[n] x
  have hu (n : ℕ) : u n∈Set.Icc (0:ℝ) 1 := iterate_mem M p x hx n
  have hlim : ∃ q,Tendsto u atTop (𝓝 q) := by
    rcases le_total x (M.D p x) with h|h
    · have hm : Monotone u := by
        apply monotone_nat_of_le_succ
        intro n
        induction n with
        | zero => simpa [u] using h
        | succ n ih =>
          simpa only [u,Function.iterate_succ_apply'] using M.hDmono p (hu n) (hu (n+1)) ih
      exact ⟨_,tendsto_atTop_ciSup hm ⟨1,by rintro _ ⟨n,rfl⟩;exact (hu n).2⟩⟩
    · have hm : Antitone u := by
        apply antitone_nat_of_succ_le
        intro n
        induction n with
        | zero => simpa [u] using h
        | succ n ih =>
          simpa only [u,Function.iterate_succ_apply'] using M.hDmono p (hu (n+1)) (hu n) ih
      exact ⟨_,tendsto_atTop_ciInf hm ⟨0,by rintro _ ⟨n,rfl⟩;exact (hu n).1⟩⟩
  obtain ⟨q,hq⟩ := hlim
  have hqmem : q∈Set.Icc (0:ℝ) 1 := isClosed_Icc.mem_of_tendsto hq (Eventually.of_forall hu)
  have hf : Tendsto (fun n => M.D p (u n)) atTop (𝓝 (M.D p q)) :=
    ((demand_cont M p) q hqmem).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hq,Eventually.of_forall hu⟩)
  have hs : Tendsto (fun n => u (n+1)) atTop (𝓝 q) := hq.comp (tendsto_add_atTop_nat 1)
  have heq : M.D p q=q := tendsto_nhds_unique hf (by simpa only [u,Function.iterate_succ_apply'] using hs)
  exact ⟨q,⟨hqmem,heq⟩,hq⟩

lemma interior_fixed (M : Market) (p q : ℝ) (hq : q∈Set.Ioo (0:ℝ) 1)
    (hf : M.D p q=q) : M.P q=p := by
  rcases lt_trichotomy (M.P q) p with h|h|h
  · have := M.hPbelow q ⟨hq.1.le,hq.2.le⟩ p h hq.1
    linarith
  · exact h
  · have := M.hPabove q ⟨hq.1.le,hq.2.le⟩ p h hq.2
    linarith

lemma fixed_between (M : Market) (p a b : ℝ) (ha : a∈Set.Icc (0:ℝ) 1)
    (hb : b∈Set.Icc (0:ℝ) 1) (hab : a≤b)
    (hfa : 0≤M.D p a-a) (hfb : M.D p b-b≤0) :
    ∃ q∈Set.Icc a b,M.D p q=q := by
  have hc : ContinuousOn (fun q => M.D p q-q) (Set.Icc a b) :=
    ((demand_cont M p).mono (Set.Icc_subset_Icc ha.1 hb.2)).sub continuousOn_id
  obtain ⟨q,hq,hf⟩ := intermediate_value_Icc' hab hc ⟨hfb,hfa⟩
  exact ⟨q,hq,by linarith⟩
end NetworkResearch
namespace NetworkResearch
open NetExtDominance.Introspective
lemma signs (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p qo qm qi : ℝ) (ho : IsQout M.P QL p qo)
    (hm : IsQmid M.P QL QH p qm) (hi : IsQin M.P QH p qi) :
    M.D p qo=qo ∧ M.D p qm=qm ∧ M.D p qi=qi ∧
      ∀ x∈Set.Icc (0:ℝ) 1,
        (qm<x → x<qi → x<M.D p x) ∧
        (qi<x → M.D p x<x) ∧
        (qo<x → x<qm → M.D p x<x) ∧
        (x<qo → x<M.D p x) := by
  rcases hIO with ⟨hL,hLH,hH,hout,_,hmid,hin,_,_,_⟩
  have hqo : qo∈Set.Icc (0:ℝ) 1 := ⟨ho.1.1,ho.1.2.trans (by linarith)⟩
  have hqm : qm∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hm.1.1],by linarith [hm.1.2]⟩
  have hqi : qi∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hi.1.1],hi.1.2⟩
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [ho.2] using M.hP qo hqo
  · simpa only [hm.2] using M.hP qm hqm
  · simpa only [hi.2] using M.hP qi hqi
  · intro x hx
    refine ⟨?_,?_,?_,?_⟩
    · intro hxm hxi
      apply M.hPabove x hx p _ (lt_of_lt_of_le hxi hqi.2)
      by_cases h : x≤QH
      · have hh := hmid hm.1 ⟨hm.1.1.trans hxm.le,h⟩ hxm
        simpa only [hm.2] using hh
      · have hh := hin ⟨(lt_of_not_ge h).le,hx.2⟩ hi.1 hxi
        simpa only [hi.2] using hh
    · intro hix
      apply M.hPbelow x hx p _ (lt_of_le_of_lt hqi.1 hix)
      have hh := hin hi.1 ⟨hi.1.1.trans hix.le,hx.2⟩ hix
      simpa only [hi.2] using hh
    · intro hox hxm
      apply M.hPbelow x hx p _ (lt_of_le_of_lt hqo.1 hox)
      by_cases h : x≤QL
      · have hh := hout ho.1 ⟨hx.1,h⟩ hox
        simpa only [ho.2] using hh
      · have hh := hmid ⟨(lt_of_not_ge h).le,hxm.le.trans hm.1.2⟩ hm.1 hxm
        simpa only [hm.2] using hh
    · intro hxo
      apply M.hPabove x hx p _ (lt_of_lt_of_le hxo hqo.2)
      have hh := hout ⟨hx.1,hxo.le.trans ho.1.2⟩ ho.1 hxo
      simpa only [ho.2] using hh
end NetworkResearch
namespace NetworkResearch
open NetExtDominance.Introspective
lemma branch_exists (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL≤p) (hp2 : p≤pmax M.P QH) :
    ∃ qo qm qi,IsQout M.P QL p qo ∧ IsQmid M.P QL QH p qm ∧ IsQin M.P QH p qi := by
  rcases hIO with ⟨hL,hLH,hH,hout,_,hmid,hin,_,hp0,hpN⟩
  have hLm : QL∈Set.Icc (0:ℝ) 1 := ⟨hL.le,by linarith⟩
  have hHm : QH∈Set.Icc (0:ℝ) 1 := ⟨by linarith,hH.le⟩
  have hDL : M.D p QL≤QL := by
    simpa only [pmin,M.hP QL hLm] using M.hDanti QL hLm hp1
  have hDH : QH≤M.D p QH := by
    simpa only [pmax,M.hP QH hHm] using M.hDanti QH hHm hp2
  have hzero : 0<M.D p 0 := M.hPabove 0 (by norm_num) p (lt_of_le_of_lt hp2 hp0) (by norm_num)
  have hone : M.D p 1<1 := M.hPbelow 1 (by norm_num) p (lt_of_lt_of_le hpN hp1) (by norm_num)
  obtain ⟨qo,hqo,hfo⟩ := fixed_between M p 0 QL (by norm_num) hLm hL.le (by linarith) (by linarith)
  have hqo0 : 0<qo := by
    by_contra h
    have he : qo=0 := by linarith [hqo.1]
    subst qo
    linarith
  have hqoin : qo∈Set.Ioo (0:ℝ) 1 := ⟨hqo0,by linarith [hqo.2]⟩
  obtain ⟨qi,hqi,hfi⟩ := fixed_between M p QH 1 hHm (by norm_num) hH.le (by linarith) (by linarith)
  have hqi1 : qi<1 := by
    by_contra h
    have he : qi=1 := by linarith [hqi.2]
    subst qi
    linarith
  have hqiin : qi∈Set.Ioo (0:ℝ) 1 := ⟨by linarith [hqi.1],hqi1⟩
  have hc : ContinuousOn (fun q => M.D p q-q) (Set.Icc QL QH) :=
    ((demand_cont M p).mono (Set.Icc_subset_Icc hLm.1 hHm.2)).sub continuousOn_id
  obtain ⟨qm,hqm,hfm⟩ := intermediate_value_Icc hLH.le hc (show (0:ℝ)∈Set.Icc (M.D p QL-QL) (M.D p QH-QH) by constructor <;> linarith)
  refine ⟨qo,qm,qi,⟨hqo,interior_fixed M p qo hqoin hfo⟩,?_,⟨hqi,interior_fixed M p qi hqiin hfi⟩⟩
  exact ⟨hqm,interior_fixed M p qm ⟨by linarith [hqm.1],by linarith [hqm.2]⟩ (by linarith)⟩

lemma fixed_antitone_unique (M : Market) (p : ℝ) (S : Set ℝ) (hanti : StrictAntiOn M.P S)
    (x y : ℝ) (hx : IsEquilibriumQty M p x) (hy : IsEquilibriumQty M p y)
    (hxs : x∈S) (hys : y∈S) : x=y := by
  have hnot (a b : ℝ) (ha : IsEquilibriumQty M p a) (hb : IsEquilibriumQty M p b)
      (has : a∈S) (hbs : b∈S) : ¬a<b := by
    intro hab
    have hPa : M.P a≤p := by
      by_contra h
      have := M.hPabove a ha.1 p (lt_of_not_ge h) (lt_of_lt_of_le hab hb.1.2)
      linarith [ha.2]
    have hPb : p≤M.P b := by
      by_contra h
      have := M.hPbelow b hb.1 p (lt_of_not_ge h) (lt_of_le_of_lt ha.1.1 hab)
      linarith [hb.2]
    have := hanti has hbs hab
    linarith
  exact le_antisymm (le_of_not_gt (hnot y x hy hx hys hxs)) (le_of_not_gt (hnot x y hx hy hxs hys))

lemma outside_unique (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp : pmax M.P QH<p ∨ p<pmin M.P QL) :
    ∃! q,IsEquilibriumQty M p q := by
  rcases hIO with ⟨hL,hLH,hH,hout,_,hmid,hin,_,_,_⟩
  obtain ⟨q,hq,_⟩ := iterate_limit M p 0 (by norm_num)
  refine ⟨q,hq,?_⟩
  intro q' hq'
  rcases hp with hp|hp
  · have hbranch (x : ℝ) (hx : IsEquilibriumQty M p x) : x∈Set.Icc 0 QL := by
      refine ⟨hx.1.1,?_⟩
      by_contra h
      have hLx : QL<x := lt_of_not_ge h
      have hPx : M.P x≤M.P QH := by
        by_cases h : x≤QH
        · exact hmid.monotoneOn ⟨hLx.le,h⟩ ⟨hLH.le,le_rfl⟩ h
        · exact hin.antitoneOn ⟨le_rfl,hH.le⟩ ⟨(lt_of_not_ge h).le,hx.1.2⟩ (lt_of_not_ge h).le
      have := M.hPbelow x hx.1 p (lt_of_le_of_lt hPx hp) (hL.trans hLx)
      linarith [hx.2]
    exact fixed_antitone_unique M p _ hout q' q hq' hq (hbranch q' hq') (hbranch q hq)
  · have hbranch (x : ℝ) (hx : IsEquilibriumQty M p x) : x∈Set.Icc QH 1 := by
      refine ⟨?_,hx.1.2⟩
      by_contra h
      have hxH : x<QH := lt_of_not_ge h
      have hPx : M.P QL≤M.P x := by
        by_cases h : x≤QL
        · exact hout.antitoneOn ⟨hx.1.1,h⟩ ⟨hL.le,le_rfl⟩ h
        · exact hmid.monotoneOn ⟨le_rfl,hLH.le⟩ ⟨(lt_of_not_ge h).le,hxH.le⟩ (lt_of_not_ge h).le
      have := M.hPabove x hx.1 p (lt_of_lt_of_le hp hPx) (hxH.trans hH)
      linarith [hx.2]
    exact fixed_antitone_unique M p _ hin q' q hq' hq (hbranch q' hq') (hbranch q hq)

lemma outside_converge (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp : pmax M.P QH<p ∨ p<pmin M.P QL)
    (q : ℝ) (hq : IsEquilibriumQty M p q) (x : ℝ) (hx : x∈Set.Icc (0:ℝ) 1) :
    IsIntrospectiveEq M p x q := by
  obtain ⟨r,hr,hlim⟩ := iterate_limit M p x hx
  have he := (outside_unique M QL QH hIO p hp).unique hr hq
  simpa only [he] using hlim
end NetworkResearch
namespace NetworkResearch
open NetExtDominance.Introspective
lemma three (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL≤p) (hp2 : p≤pmax M.P QH) :
    (∃! q,IsQout M.P QL p q) ∧ (∃! q,IsQmid M.P QL QH p q) ∧
    (∃! q,IsQin M.P QH p q) ∧
    ∀ qo qm qi,IsQout M.P QL p qo → IsQmid M.P QL QH p qm → IsQin M.P QH p qi →
      (∀ q,IsEquilibriumQty M p q ↔ q=qo ∨ q=qm ∨ q=qi) ∧
      (pmin M.P QL<p → p<pmax M.P QH → qo<qm ∧ qm<qi) ∧
      (p=pmin M.P QL → qo=qm ∧ qm<qi) ∧
      (p=pmax M.P QH → qo<qm ∧ qm=qi) := by
  obtain ⟨qo,hqm,hqi,ho,hm,hi⟩ := branch_exists M QL QH hIO p hp1 hp2
  rcases hIO with ⟨hL,hLH,hH,hout,houtC,hmid,hin,hinC,hp0,hpN⟩
  have hoU (x y : ℝ) (hx : IsQout M.P QL p x) (hy : IsQout M.P QL p y) : x=y := hout.injOn hx.1 hy.1 (hx.2.trans hy.2.symm)
  have hmU (x y : ℝ) (hx : IsQmid M.P QL QH p x) (hy : IsQmid M.P QL QH p y) : x=y := hmid.injOn hx.1 hy.1 (hx.2.trans hy.2.symm)
  have hiU (x y : ℝ) (hx : IsQin M.P QH p x) (hy : IsQin M.P QH p y) : x=y := hin.injOn hx.1 hy.1 (hx.2.trans hy.2.symm)
  refine ⟨⟨qo,ho,fun y hy=>hoU y qo hy ho⟩,⟨hqm,hm,fun y hy=>hmU y hqm hy hm⟩,
    ⟨hqi,hi,fun y hy=>hiU y hqi hy hi⟩,?_⟩
  intro qo qm qi ho hm hi
  have hqo : qo∈Set.Icc (0:ℝ) 1 := ⟨ho.1.1,by linarith [ho.1.2]⟩
  have hqm : qm∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hm.1.1],by linarith [hm.1.2]⟩
  have hqi : qi∈Set.Icc (0:ℝ) 1 := ⟨by linarith [hi.1.1],hi.1.2⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro q
    constructor
    · intro hq
      have hq0 : 0<q := by
        by_contra h
        have he : q=0 := by linarith [hq.1.1]
        have hh := M.hPabove 0 (show (0:ℝ)∈Set.Icc 0 1 by norm_num) p (lt_of_le_of_lt hp2 hp0) (by norm_num)
        rw [he] at hq
        linarith [hq.2]
      have hq1 : q<1 := by
        by_contra h
        have he : q=1 := by linarith [hq.1.2]
        have hh := M.hPbelow 1 (show (1:ℝ)∈Set.Icc 0 1 by norm_num) p (lt_of_lt_of_le hpN hp1) (by norm_num)
        rw [he] at hq
        linarith [hq.2]
      have hPq := interior_fixed M p q ⟨hq0,hq1⟩ hq.2
      by_cases hqL : q≤QL
      · exact Or.inl (hoU q qo ⟨⟨hq.1.1,hqL⟩,hPq⟩ ho)
      by_cases hqH : q≤QH
      · exact Or.inr (Or.inl (hmU q qm ⟨⟨(lt_of_not_ge hqL).le,hqH⟩,hPq⟩ hm))
      · exact Or.inr (Or.inr (hiU q qi ⟨⟨(lt_of_not_ge hqH).le,hq.1.2⟩,hPq⟩ hi))
    · intro h
      rcases h with he|he|he
      · subst q
        exact ⟨hqo,by simpa only [ho.2] using M.hP qo hqo⟩
      · subst q
        exact ⟨hqm,by simpa only [hm.2] using M.hP qm hqm⟩
      · subst q
        exact ⟨hqi,by simpa only [hi.2] using M.hP qi hqi⟩
  · intro hpL hpH
    constructor
    · by_contra h
      have he : qo=QL := by linarith [ho.1.2,hm.1.1]
      have hbad := ho.2
      rw [he] at hbad
      exact (ne_of_lt hpL) hbad
    · by_contra h
      have he : qi=QH := by linarith [hi.1.1,hm.1.2]
      have hbad := hi.2
      rw [he] at hbad
      exact (ne_of_lt hpH) hbad.symm
  · intro he
    have hoL : qo=QL := hoU qo QL ho ⟨⟨hL.le,le_rfl⟩,he.symm⟩
    have hmL : qm=QL := hmU qm QL hm ⟨⟨le_rfl,hLH.le⟩,he.symm⟩
    constructor
    · exact hoL.trans hmL.symm
    · linarith [hi.1.1]
  · intro he
    have hmH : qm=QH := hmU qm QH hm ⟨⟨hLH.le,le_rfl⟩,he.symm⟩
    have hiH : qi=QH := hiU qi QH hi ⟨⟨le_rfl,hH.le⟩,he.symm⟩
    constructor
    · linarith [ho.1.2]
    · exact hmH.trans hiH.symm
end NetworkResearch

open NetExtDominance.Introspective


/-- §2.1: the three branches exhaust all equilibrium quantities, with two
distinct quantities at either threshold. -/
theorem solution
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL ≤ p) (hp2 : p ≤ pmax M.P QH) :
    (∃! q, IsQout M.P QL p q) ∧
      (∃! q, IsQmid M.P QL QH p q) ∧
      (∃! q, IsQin M.P QH p q) ∧
      ∀ qo qm qi,
        IsQout M.P QL p qo →
        IsQmid M.P QL QH p qm →
        IsQin M.P QH p qi →
        (∀ q, IsEquilibriumQty M p q ↔ (q = qo ∨ q = qm ∨ q = qi)) ∧
        (pmin M.P QL < p → p < pmax M.P QH → qo < qm ∧ qm < qi) ∧
        (p = pmin M.P QL → qo = qm ∧ qm < qi) ∧
        (p = pmax M.P QH → qo < qm ∧ qm = qi) := by exact NetworkResearch.three M QL QH hIO p hp1 hp2



#print axioms solution
