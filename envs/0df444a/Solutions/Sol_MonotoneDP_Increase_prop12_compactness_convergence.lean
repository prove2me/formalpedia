-- Prove2me | solution 1 for MonotoneDP.Increase.prop12_compactness_convergence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:40:37.415314+00:00
-- url     : https://prove2.me/submissions/da0de76b-a1a4-433d-8793-68d928cd480b

import Theorems.Thm_MonotoneDP_Increase_lemma3_compact_sublevel_min
import Theorems.Thm_MonotoneDP_Increase_prop10_dp_limit_le_optimal
import Theorems.Thm_MonotoneDP_Increase_lemma2_projection_epigraph
import Theorems.Thm_MonotoneDP_Increase_cor5_1_stationary_bellman
import Theorems.Thm_MonotoneDP_Increase_prop5_bellman_equation
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic
open MonotoneDP.Increase Filter Topology
namespace CIncrease

theorem comp_mono {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) : Monotone (m.comp π N) := by
  induction N with
  | zero => exact monotone_id
  | succ N ih =>
    intro J K hJK
    apply ih
    exact fun x => m.mono x _ ((π N).2 x) J K hJK

theorem comp_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) :
    Monotone (fun N => m.comp π N m.Jbar) := by
  apply monotone_nat_of_le_succ
  intro N
  exact comp_mono m π N (fun x => hI x _ ((π N).2 x))

theorem Jpi_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    m.Jpi π x=⨆ N, m.comp π N m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem policy_tendsto {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (π : m.Policy) (x : S) :
    Tendsto (fun N => m.comp π N m.Jbar x) atTop (𝓝 (m.Jpi π x)) := by
  rw [Jpi_eq_iSup m hI]
  exact tendsto_atTop_iSup (fun i j hij => comp_monotone m hI π hij x)

theorem Jbar_le_Jstar {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jstar := by
  intro x
  apply le_iInf
  intro π
  rw [Jpi_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem T_le_Tmu {S C : Type*} (m : Model S C) (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => iInf_le_of_le (μ.1 x) (iInf_le_of_le (μ.2 x) le_rfl)

theorem comp_head {S C : Type*} (m : Model S C) (π : m.Policy) (N : ℕ) (J : S → EReal) :
    m.comp π (N+1) J=m.Tmu (π 0) (m.comp (fun k => π (k+1)) N J) := by
  induction N generalizing J with
  | zero => rfl
  | succ N ih => exact ih (m.Tmu (π (N+1)) J)

theorem Jpi_head {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (hI1 : m.AssumptionI1)
    (π : m.Policy) : m.Jpi π=m.Tmu (π 0) (m.Jpi (fun k => π (k+1))) := by
  funext x
  have h := hI1 (fun N => m.comp (fun k => π (k+1)) N m.Jbar)
    (fun N => comp_monotone m hI _ (Nat.zero_le N))
    (fun N => comp_monotone m hI _ (Nat.le_succ N)) x _ ((π 0).2 x)
  have hl : limUnder atTop (fun N => m.H x ((π 0).1 x) (m.comp (fun k => π (k+1)) N m.Jbar))=m.Jpi π x := by
    apply Tendsto.limUnder_eq
    change Tendsto (fun N => m.Tmu (π 0) (m.comp (fun k => π (k+1)) N m.Jbar) x) atTop (𝓝 (m.Jpi π x))
    simp_rw [← comp_head]
    exact (tendsto_add_atTop_iff_nat 1).mpr (policy_tendsto m hI π x)
  exact hl.symm.trans h
end CIncrease

private theorem criterion {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    (∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar) ∧
      ((∃ π : m.Policy, m.Jpi π=m.Jstar) → ∃ μ : m.Selector, m.Jmu μ=m.Jstar) := by
  have hb := (prop5_bellman_equation m hI hI1 hI2).1
  have hcriterion : ∀ μ : m.Selector, m.Jmu μ=m.Jstar ↔ m.Tmu μ m.Jstar=m.T m.Jstar := by
    intro μ
    have hμ := cor5_1_stationary_bellman m hI hI1 hI2 μ
    constructor
    · intro h
      rw [h] at hμ
      exact hμ.1.symm.trans hb
    · intro h
      apply le_antisymm
      · exact hμ.2 m.Jstar (CIncrease.Jbar_le_Jstar m hI) (by rw [h,← hb])
      · exact fun x => iInf_le (fun π : m.Policy => m.Jpi π x) (m.stationary μ)
  refine ⟨hcriterion,?_⟩
  rintro ⟨π,hπ⟩
  refine ⟨π 0,(hcriterion (π 0)).mpr ?_⟩
  apply le_antisymm
  · rw [← hb,← hπ]
    have hh := CIncrease.Jpi_head m hI hI1 π
    conv_rhs => rw [hh]
    intro x
    apply m.mono x _ ((π 0).2 x)
    intro y
    rw [hπ]
    exact iInf_le _ _
  · exact CIncrease.T_le_Tmu m (π 0) m.Jstar

namespace CIncrease

theorem T_mono {S C : Type*} (m : Model S C) : Monotone m.T := by
  intro J K h x
  exact iInf_mono (fun u => iInf_mono (fun hu => m.mono x u hu J K h))

theorem iterate_monotone {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    Monotone (fun k => m.T^[k] m.Jbar) :=
  (T_mono m).monotone_iterate_of_le_map (fun x => le_iInf (fun u => le_iInf (fun hu => hI x u hu)))

theorem Jinf_eq_iSup {S C : Type*} (m : Model S C) (hI : m.AssumptionI) (x : S) :
    m.Jinf x=⨆ k, m.T^[k] m.Jbar x := by
  apply Tendsto.limUnder_eq
  exact tendsto_atTop_iSup (fun i j hij => iterate_monotone m hI hij x)

theorem Jbar_le_Jinf {S C : Type*} (m : Model S C) (hI : m.AssumptionI) : m.Jbar ≤ m.Jinf := by
  intro x
  rw [Jinf_eq_iSup m hI]
  exact le_iSup_of_le 0 le_rfl

theorem E_injective {S : Type*} : Function.Injective (E : (S → EReal) → Set (S × ℝ)) := by
  intro J K h
  funext x
  apply le_antisymm
  all_goals
    by_contra hn
    obtain ⟨r,hr1,hr2⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  · have hm : (x,r)∈E K := hr1.le
    rw [← h] at hm
    exact (not_le_of_gt hr2) hm
  · have hm : (x,r)∈E J := hr1.le
    rw [h] at hm
    exact (not_le_of_gt hr2) hm

theorem projected_intersection {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) :
    m.P (⋂ k ≥ 1, m.Ck k)={p : S × ℝ | ∃ u∈m.U p.1, m.H p.1 u m.Jinf ≤ (p.2 : EReal)} := by
  have hh : ∀ x u, u∈m.U x → m.H x u m.Jinf=⨆ k, m.H x u (m.T^[k] m.Jbar) := by
    intro x u hu
    have he := hI1 (fun k => m.T^[k] m.Jbar)
      (fun k => iterate_monotone m hI (Nat.zero_le k))
      (fun k => iterate_monotone m hI (Nat.le_succ k)) x u hu
    have ht := tendsto_atTop_iSup (fun i j hij => m.mono x u hu _ _ (iterate_monotone m hI hij))
    exact he.symm.trans ht.limUnder_eq
  ext p
  constructor
  · rintro ⟨u,hu,hall⟩
    refine ⟨u,hu,?_⟩
    rw [hh _ _ hu]
    apply iSup_le
    intro k
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hall (k+1)) (by omega : 1 ≤ k+1)
    simpa [Model.Ck] using h.2
  · rintro ⟨u,hu,h⟩
    refine ⟨u,hu,Set.mem_iInter.mpr (fun k => Set.mem_iInter.mpr (fun hk => ?_))⟩
    refine ⟨hu,?_⟩
    exact (le_iSup (fun k => m.H p.1 u (m.T^[k] m.Jbar)) (k-1)).trans (by rwa [← hh _ _ hu])

theorem closed_projected_intersection {S C : Type*} (m : Model S C) (hI : m.AssumptionI) :
    (⋂ k ≥ 1, Pbar (m.P (m.Ck k)))=E m.Jinf := by
  ext p
  simp only [Set.mem_iInter,E,Set.mem_setOf_eq]
  constructor
  · intro h
    rw [Jinf_eq_iSup m hI]
    apply iSup_le
    intro k
    have hh := h (k+1) (by omega)
    rw [(lemma2_projection_epigraph m hI (k+1) (by omega)).1.2] at hh
    exact (iterate_monotone m hI (Nat.le_succ k) p.1).trans hh
  · intro h k hk
    rw [(lemma2_projection_epigraph m hI k hk).1.2]
    change m.T^[k] m.Jbar p.1 ≤ (p.2 : EReal)
    exact (le_iSup (fun k => m.T^[k] m.Jbar p.1) k).trans (by rwa [← Jinf_eq_iSup m hI])
end CIncrease

private theorem characterization {S C : Type*} (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α) :
    ((m.Jinf=m.T m.Jinf ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k))=⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      (m.Jinf=m.Jstar ↔
        Pbar (m.P (⋂ k ≥ 1, m.Ck k))=⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) ∧
    (((m.Jinf=m.T m.Jinf ∧
          ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) ↔
        m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k))) ∧
      ((m.Jinf=m.Jstar ∧ ∃ μ : m.Selector, m.Jmu μ=m.Jstar) ↔
        m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)))) := by
  classical
  have h10 := prop10_dp_limit_le_optimal m hI hI1 hI2
  let m' : Model S C := {m with
    Jbar := m.Jinf
    Jbar_ne_bot := fun x => ne_bot_of_le_ne_bot (m.Jbar_ne_bot x) (CIncrease.Jbar_le_Jinf m hI x) }
  have hI' : m'.AssumptionI := by
    intro x u hu
    exact (h10.1.1 x).trans (iInf_le_of_le u (iInf_le_of_le hu le_rfl))
  have hp : m'.P (m'.Ck 1)=m.P (⋂ k ≥ 1, m.Ck k) := by
    rw [CIncrease.projected_intersection m hI hI1]
    ext p
    simp [Model.P,Model.Ck,m']
  have hepi := lemma2_projection_epigraph m' hI' 1 le_rfl
  rw [hp] at hepi
  change
    (m.P (⋂ k ≥ 1, m.Ck k) ⊆ Pbar (m.P (⋂ k ≥ 1, m.Ck k)) ∧
      Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E (m.T m.Jinf)) ∧
    ((m.P (⋂ k ≥ 1, m.Ck k)=Pbar (m.P (⋂ k ≥ 1, m.Ck k)) ∧
      Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E (m.T m.Jinf)) ↔
      ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) at hepi
  have hstar : m.Jinf=m.Jstar ↔ m.Jinf=m.T m.Jinf := by
    constructor
    · intro h
      rw [h,h10.1.2.2]
    · intro h
      have hh := h10.2.mpr h
      exact hh.1.trans (hh.2.1.trans hh.2.2)
  have hfix : m.Jinf=m.T m.Jinf ↔ Pbar (m.P (⋂ k ≥ 1, m.Ck k))=E m.Jinf := by
    rw [hepi.1.2]
    exact ⟨fun h => congrArg E h.symm,fun h => (CIncrease.E_injective h).symm⟩
  have hatt : (m.Jinf=m.T m.Jinf ∧
      ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) ↔
      m.P (⋂ k ≥ 1, m.Ck k)=E m.Jinf := by
    constructor
    · rintro ⟨hf,ha⟩
      exact (hepi.2.mpr ha).1.trans (hfix.mp hf)
    · intro hpE
      have hf : m.Jinf=m.T m.Jinf := by
        apply hfix.mpr
        apply Set.Subset.antisymm
        · rw [hepi.1.2]
          exact fun p h => (h10.1.1 p.1).trans h
        · rw [← hpE]
          exact hepi.1.1
      refine ⟨hf,hepi.2.mp ⟨?_,hepi.1.2⟩⟩
      exact hpE.trans (hfix.mp hf).symm
  have hopt : (m.Jinf=m.Jstar ∧ ∃ μ : m.Selector, m.Jmu μ=m.Jstar) ↔
      (m.Jinf=m.T m.Jinf ∧ ∀ x : S, ∃ u∈m.U x, m.H x u m.Jinf=⨅ v∈m.U x, m.H x v m.Jinf) := by
    constructor
    · rintro ⟨hj,μ,hμ⟩
      refine ⟨hstar.mp hj,?_⟩
      intro x
      refine ⟨μ.1 x,μ.2 x,?_⟩
      rw [hj]
      exact congrFun ((criterion m hI hI1 hI2).1 μ |>.mp hμ) x
    · rintro ⟨hf,ha⟩
      have hj := hstar.mpr hf
      choose u hu he using ha
      let μ : m.Selector := ⟨u,hu⟩
      refine ⟨hj,μ,(criterion m hI hI1 hI2).1 μ |>.mpr ?_⟩
      rw [← hj]
      funext x
      exact he x
  rw [CIncrease.closed_projected_intersection m hI]
  exact ⟨⟨hfix,hstar.trans hfix⟩,⟨hatt,hopt.trans hatt⟩⟩

theorem solution {S C : Type*} [TopologicalSpace C] [T2Space C]
    (m : Model S C)
    (hI : m.AssumptionI) (hI1 : m.AssumptionI1) (hI2 : ∃ α : ℝ, m.AssumptionI2 α)
    (hcpt : ∃ kbar : ℕ, ∀ x : S, ∀ lam : ℝ, ∀ k : ℕ, kbar ≤ k →
      IsCompact {u | u∈m.U x ∧ m.H x u ((m.T)^[k] m.Jbar) ≤ (lam : EReal)}) :
    m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)) ∧
      (m.Jinf=m.T m.Jinf ∧ m.T m.Jinf=m.T m.Jstar ∧ m.T m.Jstar=m.Jstar) ∧
      ∃ μ : m.Selector, m.Jmu μ=m.Jstar := by
  classical
  obtain ⟨kbar,hcpt⟩ := hcpt
  have hp : m.P (⋂ k ≥ 1, m.Ck k)=⋂ k ≥ 1, Pbar (m.P (m.Ck k)) := by
    apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨u,hu,hh⟩ := hp
      apply Set.mem_iInter.mpr
      intro k
      apply Set.mem_iInter.mpr
      intro hk
      exact (lemma2_projection_epigraph m hI k hk).1.1
        ⟨u,hu,Set.mem_iInter.mp (Set.mem_iInter.mp hh k) hk⟩
    · intro p hp
      have hv : ∀ k, 1 ≤ k → (m.T^[k] m.Jbar) p.1 ≤ (p.2 : EReal) := by
        intro k hk
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp hp k) hk
        rw [(lemma2_projection_epigraph m hI k hk).1.2] at hh
        exact hh
      let K : ℕ → Set C := fun j => {u | u∈m.U p.1 ∧ m.H p.1 u (m.T^[j+kbar] m.Jbar) ≤ (p.2 : EReal)}
      have hK : ∀ j, IsCompact (K j) := fun j => hcpt p.1 p.2 (j+kbar) (by omega)
      have hnon : ∀ j, (K j).Nonempty := by
        intro j
        obtain ⟨u,hu,hmin⟩ := lemma3_compact_sublevel_min
          (fun u => m.H p.1 u (m.T^[j+kbar] m.Jbar)) (m.U p.1) (m.U_nonempty p.1)
          (fun r => hcpt p.1 r (j+kbar) (by omega))
        refine ⟨u,hu,?_⟩
        have hle : m.H p.1 u (m.T^[j+kbar] m.Jbar) ≤ m.T (m.T^[j+kbar] m.Jbar) p.1 := by
          exact le_iInf (fun v => le_iInf (fun hv => hmin hv))
        exact hle.trans (by simpa only [Function.iterate_succ_apply'] using hv (j+kbar+1) (by omega))
      have hdec : ∀ j, K (j+1) ⊆ K j := by
        intro j u hu
        refine ⟨hu.1,?_⟩
        exact (m.mono p.1 u hu.1 _ _ (CIncrease.iterate_monotone m hI (by omega : j+kbar ≤ j+1+kbar))).trans hu.2
      obtain ⟨u,hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hnon (hK 0) (fun j => (hK j).isClosed)
      have huj := fun j => Set.mem_iInter.mp hu j
      refine ⟨u,(huj 0).1,Set.mem_iInter.mpr (fun k => Set.mem_iInter.mpr (fun hk => ?_))⟩
      refine ⟨(huj 0).1,?_⟩
      exact (m.mono p.1 u (huj 0).1 _ _ (CIncrease.iterate_monotone m hI (by omega : k-1 ≤ k+kbar))).trans (huj k).2
  have hh := characterization m hI hI1 hI2
  exact ⟨hp,(prop10_dp_limit_le_optimal m hI hI1 hI2).2.mpr (hh.2.1.mpr hp).1,(hh.2.2.mpr hp).2⟩
