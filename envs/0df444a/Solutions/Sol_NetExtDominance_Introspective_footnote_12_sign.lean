-- Prove2me | solution 1 for NetExtDominance.Introspective.footnote_12_sign
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T10:53:07.384341+00:00
-- url     : https://prove2.me/submissions/e37c2eee-ef44-411d-95e7-6af9c0c96e0e

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

open NetExtDominance.Introspective


/-- Footnote 12: the demand map lies above or below the 45-degree line on the
successive intervals cut out by the three inverse-demand intersections. -/
theorem solution
    (M : Market) (QL QH : ℝ) (hIO : IsInOut M.P QL QH)
    (p : ℝ) (hp1 : pmin M.P QL ≤ p) (hp2 : p ≤ pmax M.P QH)
    (qo qm qi : ℝ) (ho : IsQout M.P QL p qo)
    (hm : IsQmid M.P QL QH p qm) (hi : IsQin M.P QH p qi) :
    M.D p qo = qo ∧ M.D p qm = qm ∧ M.D p qi = qi ∧
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (qm < x → x < qi → x < M.D p x) ∧
        (qi < x → M.D p x < x) ∧
        (qo < x → x < qm → M.D p x < x) ∧
        (x < qo → x < M.D p x) := by exact NetworkResearch.signs M QL QH hIO p qo qm qi ho hm hi



#print axioms solution
