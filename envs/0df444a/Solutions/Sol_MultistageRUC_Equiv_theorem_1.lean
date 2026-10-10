-- Prove2me | solution 1 for MultistageRUC.Equiv.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:26:41.060557+00:00
-- url     : https://prove2.me/submissions/53442690-08a9-4b41-9957-d90c4f90147b

import Mathlib
import Definitions.Def_MultistageRUC_Equiv_Setting

namespace RRAux_MultistageRUC_Equiv_theorem_1

open MultistageRUC.Equiv

lemma omega_isClosed {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (x : Fin Ng → Fin T → ℝ) (t : Fin T) (e : Fin Nd → ℝ) :
    IsClosed (OmegaNR D x t e) := by
  have h : OmegaNR D x t e =
      (⋂ i, ({q : Fin Ng → ℝ | D.pmin i * x i t ≤ q i} ∩ {q | q i ≤ D.pmax i * x i t})) ∩
      ((⋂ l, ({q : Fin Ng → ℝ |
          -D.fmax l ≤ dotProduct (D.alpha l) (D.Bp.mulVec q - D.Bd.mulVec e)} ∩
        {q | dotProduct (D.alpha l) (D.Bp.mulVec q - D.Bd.mulVec e) ≤ D.fmax l})) ∩
        {q | ∑ i, q i = ∑ j, e j}) := by
    ext q
    simp only [OmegaNR, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h]
  have hc : ∀ l, Continuous fun q : Fin Ng → ℝ =>
      dotProduct (D.alpha l) (D.Bp.mulVec q - D.Bd.mulVec e) := by
    intro l
    fun_prop
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (IsClosed.inter
    (isClosed_iInter fun l => ?_) ?_)
  · exact (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  · exact (isClosed_le continuous_const (hc l)).inter (isClosed_le (hc l) continuous_const)
  · exact isClosed_eq (by fun_prop) continuous_const

lemma omega_isCompact {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (x : Fin Ng → Fin T → ℝ) (t : Fin T) (e : Fin Nd → ℝ) :
    IsCompact (OmegaNR D x t e) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun i => isCompact_Icc (a := D.pmin i * x i t) (b := D.pmax i * x i t))
    (omega_isClosed D x t e) ?_
  intro q hq
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  exact fun i => hq.1 i

lemma omega_min {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (x : Fin Ng → Fin T → ℝ) (t : Fin T) (e : Fin Nd → ℝ)
    (hne : (OmegaNR D x t e).Nonempty) :
    ∃ q ∈ OmegaNR D x t e, ∀ q' ∈ OmegaNR D x t e, dispCost D q ≤ dispCost D q' := by
  have hcont : Continuous (dispCost D) := by unfold dispCost; fun_prop
  obtain ⟨q, hq, hmin⟩ := (omega_isCompact D x t e).exists_isMinOn hne hcont.continuousOn
  exact ⟨q, hq, fun q' hq' => isMinOn_iff.1 hmin q' hq'⟩

end RRAux_MultistageRUC_Equiv_theorem_1

open RRAux_MultistageRUC_Equiv_theorem_1 in
open MultistageRUC.Equiv in
-- Theorem 1, p. 11.
theorem solution {Ng Nd Nb Nl T : ℕ} (D : UCData Ng Nd Nb Nl T)
    (dbar dhat : Fin T → Fin Nd → ℝ) (Γ : ℝ) (hΓ : 0 ≤ Γ) (hdhat : ∀ t j, 0 < dhat t j) :
    (∀ x u v : Fin Ng → Fin T → ℝ, InX D x u v →
      twoStageObj D (uncSet dbar dhat Γ) false x u v =
        multiStageObj D (uncSet dbar dhat Γ) false x u v) ∧
    (⨅ (x : Fin Ng → Fin T → ℝ) (u : Fin Ng → Fin T → ℝ) (v : Fin Ng → Fin T → ℝ)
        (_ : InX D x u v), twoStageObj D (uncSet dbar dhat Γ) false x u v) =
      (⨅ (x : Fin Ng → Fin T → ℝ) (u : Fin Ng → Fin T → ℝ) (v : Fin Ng → Fin T → ℝ)
        (_ : InX D x u v), multiStageObj D (uncSet dbar dhat Γ) false x u v) := by
  have key : ∀ x u v : Fin Ng → Fin T → ℝ,
      twoStageObj D (uncSet dbar dhat Γ) false x u v =
        multiStageObj D (uncSet dbar dhat Γ) false x u v := by
    intro x u v
    unfold twoStageObj multiStageObj
    apply le_antisymm
    · -- two-stage ≤ multistage
      gcongr
      refine le_iInf₂ fun π hπ => iSup₂_mono fun d hd => ?_
      refine iInf₂_le (fun t => π t d) ?_
      intro t
      exact ⟨(hπ.2 d hd t).1, fun h => absurd h (by simp)⟩
    · -- multistage ≤ two-stage
      by_cases hfeas : ∀ d ∈ uncSet dbar dhat Γ, ∀ t, (OmegaNR D x t (d t)).Nonempty
      · classical
        let g : Fin T → (Fin Nd → ℝ) → (Fin Ng → ℝ) := fun t e =>
          if h : (OmegaNR D x t e).Nonempty then Classical.choose (omega_min D x t e h) else 0
        have hg : ∀ t e, (OmegaNR D x t e).Nonempty →
            g t e ∈ OmegaNR D x t e ∧
              ∀ q' ∈ OmegaNR D x t e, dispCost D (g t e) ≤ dispCost D q' := by
          intro t e h
          simp only [g, dif_pos h]
          exact Classical.choose_spec (omega_min D x t e h)
        let π : Policy Ng Nd T := fun t d => g t (d t)
        have hNA : Nonanticipative π := by
          intro t d d' hdd
          show g t (d t) = g t (d' t)
          rw [hdd t le_rfl]
        have hPF : PolicyFeasible D (uncSet dbar dhat Γ) false x u v π := by
          intro d hd t
          exact ⟨(hg t (d t) (hfeas d hd t)).1, fun h => absurd h (by simp)⟩
        gcongr
        refine le_trans (iInf₂_le π ⟨hNA, hPF⟩) ?_
        refine iSup₂_mono fun d hd => le_iInf₂ fun p hp => ?_
        refine EReal.coe_le_coe_iff.2 (Finset.sum_le_sum fun t _ => ?_)
        exact (hg t (d t) (hfeas d hd t)).2 (p t) (hp t).1
      · push Not at hfeas
        obtain ⟨d, hd, t, hne⟩ := hfeas
        have hinner : (⨅ p ∈ twoStageFeas D false x u v d,
            ((∑ t, dispCost D (p t) : ℝ) : EReal)) = ⊤ := by
          refine le_antisymm le_top (le_iInf₂ fun p hp => ?_)
          exact absurd ⟨p t, (hp t).1⟩ (Set.not_nonempty_iff_eq_empty.2 hne)
        have hsup : (⨆ d ∈ uncSet dbar dhat Γ, ⨅ p ∈ twoStageFeas D false x u v d,
            ((∑ t, dispCost D (p t) : ℝ) : EReal)) = ⊤ := by
          refine le_antisymm le_top ?_
          rw [← hinner]
          exact le_iSup₂_of_le d hd le_rfl
        rw [hsup, EReal.coe_add_top]
        exact le_top
  refine ⟨fun x u v _ => key x u v, ?_⟩
  exact iInf_congr fun x => iInf_congr fun u => iInf_congr fun v =>
    iInf_congr fun _ => key x u v

#print axioms solution
