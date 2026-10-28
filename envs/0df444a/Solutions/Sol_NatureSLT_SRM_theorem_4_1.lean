-- Prove2me | solution 1 for NatureSLT.SRM.theorem_4_1
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T05:04:42.016197+00:00
-- url     : https://prove2.me/submissions/e9c2af97-9bfa-4e53-bc7d-6f3293f9b37c

import Mathlib
import Definitions.Def_NatureSLT_SRM_vcDimReal
import Definitions.Def_NatureSLT_SRM_ConvergesWithRate

open MeasureTheory Filter Topology

lemma srmdis_vcDim_unit_le {Λ : Type*} (P : Λ → Unit → Bool) :
    NatureSLT.SRM.vcDim P ≤ 1 := by
  unfold NatureSLT.SRM.vcDim
  refine iSup₂_le fun h ⟨z, hz⟩ => ?_
  by_contra hlt
  have h2 : 2 ≤ h := by
    by_contra hh
    exact hlt (by exact_mod_cast (show h ≤ 1 by omega))
  obtain ⟨α, hα⟩ := hz (fun i => decide (i.val = 0))
  have e0 := hα ⟨0, by omega⟩
  have e1 := hα ⟨1, by omega⟩
  have : z ⟨0, by omega⟩ = z ⟨1, by omega⟩ := Subsingleton.elim _ _
  rw [this] at e0
  simp at e0 e1
  rw [e0] at e1
  exact Bool.noConfusion e1

theorem solution : ¬ (∀ {Z Λ : Type} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Nonempty Λ] (Q : Λ → Z → ℝ) (hQ0 : ∀ α z, 0 ≤ Q α z)
    (hQmeas : ∀ α, Measurable (Q α)) (hQint : ∀ α, Integrable (Q α) F)
    (Λs : ℕ → Set Λ) (hnest : Monotone Λs) (hne : ∀ k, (Λs k).Nonempty)
    (hdense : ∀ α : Λ, ∀ ε : ℝ, 0 < ε → ∃ k, ∃ β ∈ Λs k, ∫ z, |Q α z - Q β z| ∂F ≤ ε)
    (h : ℕ → ℕ) (T : ℕ → ℝ)
    (hcase :
      (∀ k, (∀ α ∈ Λs k, ∀ z, Q α z ≤ T k) ∧
        NatureSLT.SRM.vcDimReal (fun α : Λs k => Q α) 0 ((T k : ℝ) : EReal) = h k) ∨
      (∃ p : ℝ, 2 < p ∧ ∀ k,
        (∀ α ∈ Λs k, Integrable (fun z => Q α z ^ p) F ∧
          (∫ z, Q α z ^ p ∂F) ^ (1 / p) ≤ T k * ∫ z, Q α z ∂F) ∧
        NatureSLT.SRM.vcDimReal (fun α : Λs k => Q α) 0 ⊤ = h k))
    (n : ℕ → ℕ)
    (h47 : Tendsto (fun ℓ : ℕ => T (n ℓ) ^ 2 * h (n ℓ) * Real.log ℓ / ℓ) atTop (𝓝 0))
    (αhat : ∀ ℓ : ℕ, (Fin ℓ → Z) → Λ) (hαmem : ∀ ℓ z, αhat ℓ z ∈ Λs (n ℓ))
    (herm : ∀ ℓ (z : Fin ℓ → Z), ∀ α ∈ Λs (n ℓ),
      (1 / (ℓ : ℝ)) * ∑ i, Q (αhat ℓ z) (z i) ≤ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i))
    (hαmeas : ∀ ℓ, Measurable (fun z : Fin ℓ → Z => ∫ x, Q (αhat ℓ z) x ∂F)),
    let R : Λ → ℝ := fun α => ∫ z, Q α z ∂F
    let R₀ : ℝ := ⨅ α, R α
    let r : ℕ → ℝ := fun k => (⨅ α : Λs k, R α) - R₀
    let V : ℕ → ℝ := fun ℓ => r (n ℓ) + T (n ℓ) * Real.sqrt (h (n ℓ) * Real.log ℓ / ℓ)
    (∀ ε : ℝ, 0 < ε → Tendsto (fun ℓ : ℕ => (Measure.pi fun _ : Fin ℓ => F)
      {z | ε < |R (αhat ℓ z) - R₀|}) atTop (𝓝 0)) ∧
    NatureSLT.SRM.ConvergesWithRate F (fun ℓ z => R (αhat ℓ z)) R₀ V) := by
  intro H
  let Q : Bool → Unit → ℝ := fun b _ => if b then 0 else 1
  let Λs : ℕ → Set Bool := fun k => if k = 0 then {false} else Set.univ
  let hh : ℕ → ℕ := fun k =>
    (NatureSLT.SRM.vcDimReal (fun α : Λs k => Q α) 0 (((1 : ℝ) : ℝ) : EReal)).toNat
  have hfin : ∀ k, NatureSLT.SRM.vcDimReal (fun α : Λs k => Q α) 0 (((1 : ℝ) : ℝ) : EReal) ≠ ⊤ := by
    intro k hk
    have := srmdis_vcDim_unit_le
      (NatureSLT.SRM.realIndicators (fun α : Λs k => Q α) 0 (((1 : ℝ) : ℝ) : EReal))
    unfold NatureSLT.SRM.vcDimReal at hk
    rw [hk] at this
    exact absurd this (by decide)
  have key := @H Unit Bool _ (Measure.dirac ()) _ _ Q
    (by intro α z; dsimp [Q]; split_ifs <;> norm_num)
    (fun α => measurable_const)
    (fun α => by dsimp [Q]; split_ifs <;> exact integrable_const _)
    Λs
    (by
      intro a b hab
      dsimp [Λs]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact Set.subset_univ _
      · omega
      · exact le_rfl)
    (by
      intro k; dsimp [Λs]; split_ifs
      · exact ⟨false, rfl⟩
      · exact ⟨false, trivial⟩)
    (by
      intro α ε hε
      refine ⟨1, α, by simp [Λs], ?_⟩
      simp only [sub_self, abs_zero, integral_zero]
      exact hε.le)
    hh (fun _ => 1)
    (Or.inl fun k => ⟨by
        intro α _ z; dsimp [Q]; split_ifs <;> norm_num,
      by
        exact (ENat.coe_toNat (hfin k)).symm⟩)
    (fun _ => 0)
    (by
      have : Tendsto (fun ℓ : ℕ => Real.log ℓ / ℓ) atTop (𝓝 0) :=
        (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
          tendsto_natCast_atTop_atTop |>.congr (fun ℓ => by simp)
      have := this.const_mul ((1 : ℝ) ^ 2 * (hh 0 : ℝ))
      simp only [mul_zero] at this
      refine this.congr fun ℓ => ?_
      ring)
    (fun _ _ => false)
    (fun _ _ => by simp [Λs])
    (by
      intro ℓ z α hα
      simp [Λs] at hα
      subst hα; exact le_rfl)
    (fun ℓ => measurable_const)
  have h1 := key.1 (1 / 2) (by norm_num)
  have hR0 : (⨅ α : Bool, ∫ z, Q α z ∂(Measure.dirac ())) = 0 := by
    apply le_antisymm
    · refine (ciInf_le (Set.finite_range _).bddBelow true).trans ?_
      simp [Q]
    · refine le_ciInf fun b => ?_
      cases b <;> simp [Q]
  have hset : ∀ ℓ : ℕ, {z : Fin ℓ → Unit | (1 / 2 : ℝ) <
      |(fun α => ∫ z, Q α z ∂(Measure.dirac ())) false -
        ⨅ α : Bool, ∫ z, Q α z ∂(Measure.dirac ())|} = Set.univ := by
    intro ℓ
    ext z
    simp only [Set.mem_univ, iff_true]
    rw [hR0]
    simp [Q]
    norm_num
  simp only [hset, measure_univ] at h1
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at this
