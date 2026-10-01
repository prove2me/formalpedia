-- Prove2me | solution 1 for MonotoneDP.Decrease.prop3_finite_horizon_dp
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:53:05.885872+00:00
-- url     : https://prove2.me/submissions/8fd9bb84-b539-43b4-abb1-8863f2e01160

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

theorem comp_head {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N+1) J=m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih => exact ih (m.Tmu (π (N+1)) J)

theorem iterate_le_comp {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.T^[N] J ≤ m.comp π N J := by
  induction N generalizing J with
  | zero => exact le_rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    exact ((T_mono m).iterate N (T_le_Tmu m (π N) J)).trans (ih (m.Tmu (π N) J))

theorem selector_epsilon {S C : Type*} (m : Model S C) (J : S → EReal)
    (hbot : ∀ x, m.T J x ≠ ⊥) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : m.Selector, m.Tmu μ J ≤ fun x => m.T J x+(ε : EReal) := by
  classical
  have hsel : ∀ x, ∃ u∈m.U x, m.H x u J ≤ m.T J x+(ε : EReal) := by
    intro x
    by_cases ht : m.T J x=⊤
    · obtain ⟨u,hu⟩ := m.U_nonempty x
      exact ⟨u,hu,by simp [ht]⟩
    · have hv : m.T J x=((m.T J x).toReal : EReal) := (EReal.coe_toReal ht (hbot x)).symm
      have hlt : m.T J x < m.T J x+(ε : EReal) := by
        rw [hv,← EReal.coe_add,EReal.coe_lt_coe_iff]
        linarith
      change (⨅ u∈m.U x, m.H x u J) < _ at hlt
      obtain ⟨u,hu⟩ := iInf_lt_iff.mp hlt
      obtain ⟨hu,hval⟩ := iInf_lt_iff.mp hu
      exact ⟨u,hu,hval.le⟩
  choose u hu he using hsel
  exact ⟨⟨u,hu⟩,he⟩

theorem finite_approx_d2 {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (α : ℝ) (hD2 : m.AssumptionD2 α) (N : ℕ)
    (hbot : ∀ x, m.T^[N] m.Jbar x ≠ ⊥) :
    ∀ ε : ℝ, 0 < ε → ∃ π : m.Policy,
      m.comp π N m.Jbar ≤ fun x => m.T^[N] m.Jbar x+(ε : EReal) := by
  classical
  induction N with
  | zero =>
    intro ε hε
    refine ⟨fun _ => ⟨fun x => (m.U_nonempty x).choose,fun x => (m.U_nonempty x).choose_spec⟩,?_⟩
    intro x
    change m.Jbar x ≤ m.Jbar x+(ε : EReal)
    simpa using add_le_add (le_rfl : m.Jbar x ≤ m.Jbar x) (show (0 : EReal) ≤ (ε : EReal) by exact_mod_cast hε.le)
  | succ N ih =>
    intro ε hε
    have hbotN : ∀ x, m.T^[N] m.Jbar x ≠ ⊥ := fun x =>
      ne_bot_of_le_ne_bot (hbot x) (iterate_antitone m hD (Nat.le_succ N) x)
    let δ : ℝ := ε/(2*α)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hD2.1)
    have hαδ : α*δ=ε/2 := by dsimp [δ]; field_simp [ne_of_gt hD2.1]
    obtain ⟨ρ,hρ⟩ := ih hbotN δ hδ
    obtain ⟨μ,hμ⟩ := selector_epsilon m (m.T^[N] m.Jbar)
      (fun x => by simpa only [Function.iterate_succ_apply'] using hbot x) (ε/2) (half_pos hε)
    let π : m.Policy := fun k => Nat.casesOn k μ ρ
    refine ⟨π,?_⟩
    rw [comp_head]
    change m.Tmu μ (m.comp ρ N m.Jbar) ≤ _
    intro x
    have hg : m.comp ρ N m.Jbar ≤ m.Jbar := comp_antitone m hD ρ (Nat.zero_le N)
    have hsub : (fun y => m.comp ρ N m.Jbar y-(δ : EReal)) ≤ m.T^[N] m.Jbar :=
      fun y => EReal.sub_le_of_le_add (hρ y)
    have hh := (hD2.2 δ hδ (m.comp ρ N m.Jbar) hg x _ (μ.2 x)).1
    have hle := hh.trans (m.mono x _ (μ.2 x) _ _ hsub)
    have hfinal := (EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot (α*δ))) (Or.inl (EReal.coe_ne_top (α*δ)))).mp hle
    change m.H x (μ.1 x) (m.comp ρ N m.Jbar) ≤ _
    calc
      m.H x (μ.1 x) (m.comp ρ N m.Jbar) ≤ m.H x (μ.1 x) (m.T^[N] m.Jbar)+((α*δ : ℝ) : EReal) := hfinal
      _ ≤ (m.T (m.T^[N] m.Jbar) x+(ε/2 : ℝ))+((α*δ : ℝ) : EReal) := add_le_add (hμ x) le_rfl
      _ = m.T^[N+1] m.Jbar x+(ε : EReal) := by
        rw [hαδ,add_assoc,← EReal.coe_add,show ε/2+ε/2=ε by ring,Function.iterate_succ_apply']

theorem finite_dp_d2 {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (α : ℝ) (hD2 : m.AssumptionD2 α) (N : ℕ)
    (hbot : ∀ x, m.T^[N] m.Jbar x ≠ ⊥) : m.JN N=m.T^[N] m.Jbar := by
  funext x
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro z hz
    have ht : m.T^[N] m.Jbar x ≠ ⊤ := ne_top_of_lt hz
    have he : m.T^[N] m.Jbar x=((m.T^[N] m.Jbar x).toReal : EReal) := (EReal.coe_toReal ht (hbot x)).symm
    have hpos : 0 < z-(m.T^[N] m.Jbar x).toReal := by
      rw [he,EReal.coe_lt_coe_iff] at hz
      linarith
    obtain ⟨π,hπ⟩ := finite_approx_d2 m hD α hD2 N hbot _ hpos
    have hle := (iInf_le (fun π : m.Policy => m.comp π N m.Jbar x) π).trans (hπ x)
    change m.JN N x ≤ m.T^[N] m.Jbar x+((z-(m.T^[N] m.Jbar x).toReal : ℝ) : EReal) at hle
    have hs : m.T^[N] m.Jbar x+((z-(m.T^[N] m.Jbar x).toReal : ℝ) : EReal)=(z : EReal) := by
      conv_lhs => lhs; rw [he]
      rw [← EReal.coe_add]
      congr 1
      ring
    rwa [hs] at hle
  · exact le_iInf (fun π => iterate_le_comp m π N m.Jbar x)
end CDecrease

theorem solution {S C : Type*} (m : Model S C) (hD : m.AssumptionD)
    (N : ℕ) (hN : 1 ≤ N)
    (h : m.AssumptionD1 ∨ ((∃ α : ℝ, m.AssumptionD2 α) ∧ ∀ x, m.T^[N] m.Jbar x ≠ ⊥)) :
    m.JN N=m.T^[N] m.Jbar := by
  rcases h with h | ⟨⟨α,hα⟩,hbot⟩
  · exact CDecrease.finite_dp_d1 m hD h N m.Jbar le_rfl
  · exact CDecrease.finite_dp_d2 m hD α hα N hbot
