-- Prove2me | solution 1 for MonotoneDP.Decrease.prop6_bellman_equation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:49:54.984933+00:00
-- url     : https://prove2.me/submissions/699bf396-865f-4218-995e-36bfa577f328

import Mathlib.Topology.Order.IsLUB
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic
open MonotoneDP.Decrease Filter Topology
namespace CDecrease

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_antitone {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (π : m.Policy) :
    Antitone (fun N => m.comp π N m.Jbar) := by
  apply antitone_nat_of_succ_le
  intro N
  exact comp_mono m π N (fun x => hD x _ ((π N).2 x))

theorem Jpi_eq_iInf {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (π : m.Policy) (x : S) :
    m.Jpi π x=⨅ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iInf (fun i j hij => comp_antitone m hD π hij x)

theorem JN_antitone {S C : Type*} (m : Model S C) (hD : m.AssumptionD) : Antitone m.JN := by
  intro N K hNK x
  apply iInf_mono
  intro π
  exact comp_antitone m hD π hNK x
end CDecrease

namespace CDecrease

theorem T_mono {S C : Type*} (m : Model S C) : Monotone m.T := by
  intro J K h x
  exact iInf_mono (fun u => iInf_mono (fun hu => m.mono x u hu J K h))

theorem T_le_Tmu {S C : Type*} (m : Model S C) (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => iInf_le_of_le (μ.1 x) (iInf_le_of_le (μ.2 x) le_rfl)

theorem T_le_Jbar {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (J : S → EReal) (hJ : J ≤ m.Jbar) :
    m.T J ≤ m.Jbar := by
  intro x
  obtain ⟨u,hu⟩ := m.U_nonempty x
  exact (iInf_le_of_le u (iInf_le_of_le hu le_rfl)).trans ((m.mono x u hu J m.Jbar hJ).trans (hD x u hu))

theorem comp_lim {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (hD1 : m.AssumptionD1)
    (π : m.Policy) (N : ℕ) (Js : ℕ → S → EReal) (hJs : ∀ k, Js k ≤ m.Jbar)
    (hanti : ∀ k, Js (k+1) ≤ Js k) (x : S) :
    limUnder atTop (fun k => m.comp π N (Js k) x)=m.comp π N (fun y => limUnder atTop (fun k => Js k y)) x := by
  induction N generalizing Js with
  | zero => rfl
  | succ N ih =>
    have hb : ∀ k, m.Tmu (π N) (Js k) ≤ m.Jbar := by
      intro k y
      exact (m.mono y _ ((π N).2 y) _ _ (hJs k)).trans (hD y _ ((π N).2 y))
    have ha : ∀ k, m.Tmu (π N) (Js (k+1)) ≤ m.Tmu (π N) (Js k) :=
      fun k y => m.mono y _ ((π N).2 y) _ _ (hanti k)
    change limUnder atTop (fun k => m.comp π N (m.Tmu (π N) (Js k)) x)=_
    rw [ih _ hb ha]
    conv_rhs => rw [Model.comp]
    congr 1
    funext y
    exact hD1 Js hJs hanti y _ ((π N).2 y)

theorem selector_approx {S C : Type*} (m : Model S C) (J : S → EReal) :
    ∃ σ : ℕ → m.Selector, (∀ x, Antitone (fun k => m.Tmu (σ k) J x)) ∧
      ∀ x, Tendsto (fun k => m.Tmu (σ k) J x) atTop (𝓝 (m.T J x)) := by
  classical
  have hh : ∀ x, ∃ us : ℕ → {u // u∈m.U x},
      Antitone (fun k => m.H x (us k).1 J) ∧
      Tendsto (fun k => m.H x (us k).1 J) atTop (𝓝 (m.T J x)) := by
    intro x
    letI : Nonempty {u // u∈m.U x} := ⟨⟨(m.U_nonempty x).choose,(m.U_nonempty x).choose_spec⟩⟩
    obtain ⟨v,hanti,ht,hmem⟩ := exists_seq_tendsto_sInf
      (Set.range_nonempty (fun u : {u // u∈m.U x} => m.H x u.1 J))
      (OrderBot.bddBelow _)
    choose us hus using hmem
    refine ⟨us,?_,?_⟩
    · simpa only [hus] using hanti
    · have heq : sInf (Set.range (fun u : {u // u∈m.U x} => m.H x u.1 J))=m.T J x := by
        rw [sInf_range]
        exact iInf_subtype
      simpa only [hus,heq] using ht
  choose us ha ht using hh
  exact ⟨fun k => ⟨fun x => (us x k).1,fun x => (us x k).2⟩,ha,ht⟩

theorem comp_T_eq_iInf_selector {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (hD1 : m.AssumptionD1) (π : m.Policy) (N : ℕ) (J : S → EReal) (hJ : J ≤ m.Jbar) (x : S) :
    m.comp π N (m.T J) x=⨅ μ : m.Selector, m.comp π N (m.Tmu μ J) x := by
  apply le_antisymm
  · exact le_iInf (fun μ => comp_mono m π N (T_le_Tmu m μ J) x)
  · obtain ⟨σ,ha,ht⟩ := selector_approx m J
    have hb : ∀ k, m.Tmu (σ k) J ≤ m.Jbar :=
      fun k y => (m.mono y _ ((σ k).2 y) _ _ hJ).trans (hD y _ ((σ k).2 y))
    have hh := comp_lim m hD hD1 π N (fun k => m.Tmu (σ k) J) hb
      (fun k y => ha y (Nat.le_succ k)) x
    have he : (fun y => limUnder atTop (fun k => m.Tmu (σ k) J y))=m.T J := funext (fun y => (ht y).limUnder_eq)
    rw [he] at hh
    have hlim := tendsto_atTop_iInf (fun i j hij => comp_mono m π N (fun y => ha y hij) x)
    rw [hlim.limUnder_eq] at hh
    rw [← hh]
    exact le_iInf (fun k => iInf_le _ (σ k))
end CDecrease

namespace CDecrease

theorem comp_congr {S C : Type*} (m : Model S C) (π ρ : m.Policy) (N : ℕ)
    (h : ∀ i, i < N → π i=ρ i) (J : S → EReal) : m.comp π N J=m.comp ρ N J := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih =>
    simp only [Model.comp,h N (Nat.lt_succ_self N)]
    exact ih (fun i hi => h i (by omega)) _

theorem finite_dp_d1 {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (hD1 : m.AssumptionD1) (N : ℕ) (J : S → EReal) (hJ : J ≤ m.Jbar) :
    (fun x => ⨅ π : m.Policy, m.comp π N J x)=m.T^[N] J := by
  classical
  letI : Nonempty m.Policy := ⟨fun _ => ⟨fun x => (m.U_nonempty x).choose,fun x => (m.U_nonempty x).choose_spec⟩⟩
  induction N generalizing J with
  | zero => simp only [Model.comp,iInf_const,Function.iterate_zero,id_eq]
  | succ N ih =>
    funext x
    calc
      (⨅ π : m.Policy, m.comp π (N+1) J x)=
          ⨅ π : m.Policy, ⨅ μ : m.Selector, m.comp π N (m.Tmu μ J) x := by
        apply le_antisymm
        · apply le_iInf
          intro π
          apply le_iInf
          intro μ
          apply iInf_le_of_le (Function.update π N μ)
          change m.comp (Function.update π N μ) (N+1) J x ≤ m.comp π N (m.Tmu μ J) x
          simp only [Model.comp,Function.update_self]
          rw [comp_congr m (Function.update π N μ) π N
            (fun i hi => Function.update_of_ne (ne_of_lt hi) μ π)]
          erw [Function.update_self]
        · apply le_iInf
          intro π
          exact iInf_le_of_le π (iInf_le_of_le (π N) le_rfl)
      _ = ⨅ π : m.Policy, m.comp π N (m.T J) x := by
        simp_rw [← comp_T_eq_iInf_selector m hD hD1 _ _ J hJ]
      _ = m.T^[N] (m.T J) x := congrFun (ih (m.T J) (T_le_Jbar m hD J hJ)) x
      _ = m.T^[N+1] J x := by rw [Function.iterate_succ_apply]
end CDecrease

namespace CDecrease

theorem iterate_antitone {S C : Type*} (m : Model S C) (hD : m.AssumptionD) :
    Antitone (fun k => m.T^[k] m.Jbar) :=
  (T_mono m).antitone_iterate_of_map_le (T_le_Jbar m hD m.Jbar le_rfl)

theorem Jstar_eq_iInf {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (hD1 : m.AssumptionD1) (x : S) :
    m.Jstar x=⨅ N, m.T^[N] m.Jbar x := by
  simp only [Model.Jstar,Jpi_eq_iInf m hD]
  rw [iInf_comm]
  apply iInf_congr
  intro N
  exact congrFun (finite_dp_d1 m hD hD1 N m.Jbar le_rfl) x

theorem Jstar_eq_Jinf {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (hD1 : m.AssumptionD1) :
    m.Jstar=m.Jinf := by
  funext x
  rw [Jstar_eq_iInf m hD hD1]
  exact (tendsto_atTop_iInf (fun i j hij => iterate_antitone m hD hij x)).limUnder_eq.symm

theorem bellman {S C : Type*} (m : Model S C) (hD : m.AssumptionD) (hD1 : m.AssumptionD1) :
    m.Jstar=m.T m.Jstar := by
  have hJ : m.Jstar=(fun x => limUnder atTop (fun N => m.T^[N] m.Jbar x)) := Jstar_eq_Jinf m hD hD1
  have hh : ∀ x u, u∈m.U x → m.H x u m.Jstar=⨅ N, m.H x u (m.T^[N] m.Jbar) := by
    intro x u hu
    have he := hD1 (fun N => m.T^[N] m.Jbar)
      (fun N => iterate_antitone m hD (Nat.zero_le N))
      (fun N => iterate_antitone m hD (Nat.le_succ N)) x u hu
    rw [← hJ] at he
    have ht := tendsto_atTop_iInf (fun i j hij => m.mono x u hu _ _ (iterate_antitone m hD hij))
    exact he.symm.trans ht.limUnder_eq
  funext x
  have hTI : m.T m.Jstar x=⨅ N, m.T (m.T^[N] m.Jbar) x := by
    apply le_antisymm
    · apply le_iInf
      intro N
      apply T_mono m
      intro y
      rw [Jstar_eq_iInf m hD hD1]
      exact iInf_le _ N
    · apply le_iInf
      intro u
      apply le_iInf
      intro hu
      rw [hh x u hu]
      apply le_iInf
      intro N
      exact (iInf_le (fun N => m.T (m.T^[N] m.Jbar) x) N).trans
        (iInf_le_of_le u (iInf_le_of_le hu le_rfl))
  rw [hTI,Jstar_eq_iInf m hD hD1]
  have hs : ∀ N, m.T (m.T^[N] m.Jbar) x=m.T^[N+1] m.Jbar x := by
    intro N
    rw [Function.iterate_succ_apply']
  simp_rw [hs]
  apply le_antisymm
  · exact le_iInf (fun N => iInf_le _ (N+1))
  · exact le_iInf (fun N => (iInf_le _ N).trans (iterate_antitone m hD (Nat.le_succ N) x))

theorem subsolution_le {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (J : S → EReal) (hJ : J ≤ m.Jbar) (hpost : J ≤ m.T J) : J ≤ m.Jstar := by
  intro x
  apply le_iInf
  intro π
  rw [Jpi_eq_iInf m hD]
  apply le_iInf
  intro N
  have hp : ∀ k, J ≤ m.comp π k J := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      exact ih.trans (comp_mono m π k (hpost.trans (T_le_Tmu m (π k) J)))
  exact (hp N x).trans (comp_mono m π N hJ x)
end CDecrease

theorem solution {S C : Type*} (m : Model S C)
    (hD : m.AssumptionD) (hD1 : m.AssumptionD1) :
    m.Jstar=m.T m.Jstar ∧
      ∀ J' : S → EReal, J' ≤ m.Jbar → J' ≤ m.T J' → J' ≤ m.Jstar := by
  exact ⟨CDecrease.bellman m hD hD1,CDecrease.subsolution_le m hD⟩
