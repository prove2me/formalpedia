-- Prove2me | solution 1 for KernelRank.realExpForm_rank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:44:10.186637+00:00
-- url     : https://prove2.me/submissions/9138be94-9a25-4e2a-b8f6-49971b775332

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_singleRealCoeff_of_ne_idx
import Theorems.Thm_KernelRank_singleRealCoeff_of_ne_deg
import Theorems.Thm_KernelRank_cplxTruncForm_rank_ge
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_sum_comp_update
import Theorems.Thm_KernelRank_sum_update_nat
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_C : ι_C → ℕ) (hcC : ∀ k, c_C k ≤ m_C k)
    (w_C : ι_C → ℕ → ℂ) (hwC : ∀ k, 0 < c_C k → w_C k (c_C k - 1) ≠ 0) :
    ∀ (S : ℕ) (c_R : ι_R → ℕ), ∑ i, c_R i = S → (∀ i, c_R i ≤ m_R i) →
      ∀ (w_R : ι_R → ℕ → ℝ), (∀ i, 0 < c_R i → w_R i (c_R i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (RealExpSpace m_R m_C →ₗ[ℝ] ℝ)),
      (∀ u, realExpForm d m_R m_C c_R c_C w_R w_C u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) +
        (∑ k, if c_C k = 0 then 0 else 2 * (d - 1) * (c_C k - 1) + d) ≤ R := by
  let := Classical.decEq ι_R
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c_R hS hcRm w_R hwR R ℓ hrepr
    by_cases hall : ∀ i, c_R i = 0
    · simp only [hall, ↓reduceIte, Finset.sum_const_zero, zero_add]
      let inrC : CplxExpSpace m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        LinearMap.inr ℝ (∀ i, Fin (m_R i) → ℝ) (CplxExpSpace m_C)
      let ℓC (n : Fin R) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ := (ℓ n j).comp inrC
      have hreprC (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c_C w_C u = ∑ n, ∏ j, ℓC n j (u j) := by
        have h := hrepr (fun j => (0, u j))
        have hr0 : realTruncForm d m_R c_R w_R (fun _ => 0) = 0 := by
          simp [realTruncForm, hall]
        simp only [realExpForm, hr0, zero_add] at h
        exact h
      exact cplxTruncForm_rank_ge hd m_C (∑ k, c_C k) c_C rfl hcC w_C hwC R ℓC hreprC
    push Not at hall
    obtain ⟨i₀, hi₀_ne⟩ := hall
    have hi₀_pos : 0 < c_R i₀ := Nat.pos_of_ne_zero hi₀_ne
    have hm₀_pos : 0 < m_R i₀ := lt_of_lt_of_le hi₀_pos (hcRm i₀)
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let jLast : Fin d := ⟨d - 1, by omega⟩
    by_cases hc1 : c_R i₀ = 1
    · -- Case `c_R i₀ = 1`: kill `1` term on mode `0` and zero block `i₀` on modes `j ≥ 1`.
      let q₀ : Fin (m_R i₀) := ⟨0, hm₀_pos⟩
      let e₀ : RealExpSpace m_R m_C := embRealCoeff i₀ q₀ 1
      have hTe : realExpForm d m_R m_C c_R c_C w_R w_C (fun _ => e₀) = w_R i₀ 0 := by
        have hc0 : cplxTruncForm d m_C c_C w_C (fun _ => e₀.2) = 0 := by
          refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun q _ => ?_
          have h0 : e₀.2 k (q j₀) = 0 := rfl
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero, Complex.zero_re]
        simp only [realExpForm, hc0, add_zero, realTruncForm]
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [e₀, embRealCoeff, q₀]
          · intro q _ hne
            have hex : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := hex
            have h0 : e₀.1 i₀ (q j) = 0 := singleRealCoeff_of_ne_deg i₀ q₀ (q j) 1 hj
            rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro i _ hi
          refine Finset.sum_eq_zero fun q _ => ?_
          have h0 : e₀.1 i (q j₀) = 0 := singleRealCoeff_of_ne_idx i₀ q₀ 1 hi (q j₀)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero]
        · simp
      have hw0 : w_R i₀ 0 ≠ 0 := by simpa [hc1] using hwR i₀ hi₀_pos
      have hsum_ne : ∑ n : Fin R, ∏ j : Fin d, ℓ n j e₀ ≠ 0 := by
        rw [← hrepr]; exact hTe ▸ hw0
      obtain ⟨n₀, _, hn₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
      have hℓ0 : ℓ n₀ j₀ e₀ ≠ 0 := fun h =>
        hn₀ (Finset.prod_eq_zero (Finset.mem_univ j₀) h)
      let killR : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x => (fun i => if i = i₀ then 0 else x.1 i, x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀ <;> simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀ <;> simp [hi]
            · rfl }
      let φ₀ : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        killR - ((ℓ n₀ j₀ e₀)⁻¹ • (ℓ n₀ j₀).comp killR).smulRight e₀
      have hφ₀_kill (x : RealExpSpace m_R m_C) : ℓ n₀ j₀ (φ₀ x) = 0 := by
        simp only [φ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      let φ (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        if j = j₀ then φ₀ else killR
      let c_R' : ι_R → ℕ := Function.update c_R i₀ 0
      have hS' : ∑ i, c_R' i < S := by
        have h := sum_update_nat c_R i₀ 0
        change (∑ i, c_R' i) + c_R i₀ = (∑ i, c_R i) + 0 at h
        omega
      have hcR'm : ∀ i, c_R' i ≤ m_R i := fun i => by
        by_cases hi : i = i₀ <;> simp [c_R', hi, hcRm i]
      have hwR' : ∀ i, 0 < c_R' i → w_R i (c_R' i - 1) ≠ 0 := fun i hi => by
        by_cases hi0 : i = i₀
        · subst hi0; simp [c_R'] at hi
        · simp only [c_R', Function.update_of_ne hi0] at hi ⊢
          exact hwR i hi
      have hφ_snd (j : Fin d) (x : RealExpSpace m_R m_C) : (φ j x).2 = x.2 := by
        by_cases hj : j = j₀ <;> simp [φ, hj, φ₀, killR, e₀, embRealCoeff]
      have hT_red (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R w_C u =
            realExpForm d m_R m_C c_R c_C w_R w_C (fun j => φ j (u j)) := by
        simp only [realExpForm, hφ_snd]
        congr 1
        simp only [realTruncForm]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase Finset.univ
            (fun i => ∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i),
              w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j))
            (Finset.mem_univ i₀)]
        have hl0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_R i₀) => ∑ j, (q j : ℕ) < c_R' i₀),
            w_R i₀ (∑ j, (q j : ℕ)) * ∏ j, (u j).1 i₀ (q j) = 0 := by simp [c_R']
        have hr0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_R i₀) => ∑ j, (q j : ℕ) < c_R i₀),
            w_R i₀ (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i₀ (q j) = 0 :=
          Finset.sum_eq_zero fun q _ => by
            have hjL_ne : jLast ≠ j₀ := by
              intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
            have h0 : (φ jLast (u jLast)).1 i₀ (q jLast) = 0 := by
              simp [φ, hjL_ne, killR]
            rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero]
        rw [hl0, hr0, zero_add, zero_add]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_ne : i ≠ i₀ := Finset.ne_of_mem_erase hi
        simp only [c_R', Function.update_of_ne hi_ne]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = j₀
        · simp [φ, hj, φ₀, killR, hi_ne, e₀, embRealCoeff,
            singleRealCoeff_of_ne_idx i₀ q₀ 1 hi_ne]
        · simp [φ, hj, killR, hi_ne]
      let rem : Finset (Fin R) := Finset.univ.erase n₀
      have hcard_rem : rem.card + 1 = R := by
        simpa [rem] using Finset.card_erase_add_one (Finset.mem_univ n₀)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R w_C u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ n₀)]
        have hn0_zero : ∏ j : Fin d, ℓ n₀ j (φ j (u j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [φ, hφ₀_kill])
        rw [hn0_zero, zero_add]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ i, c_R' i) hS' c_R' rfl hcR'm w_R hwR' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) + 1 =
          ∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1 := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else (d - 1) * (v - 1) + 1) c_R i₀ 0
        change (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) +
            (if c_R i₀ = 0 then 0 else (d - 1) * (c_R i₀ - 1) + 1) =
          (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) + 0 at h
        simp only [hc1, one_ne_zero, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero] at h
        exact h
      omega
    · -- Case `c_R i₀ ≥ 2`: peel `d - 1` terms on modes `0, …, d - 2` along `sTop`, then shift up.
      have hc2 : 2 ≤ c_R i₀ := by omega
      let qTop : Fin (m_R i₀) := ⟨c_R i₀ - 1, lt_of_lt_of_le (by omega) (hcRm i₀)⟩
      let q₀ : Fin (m_R i₀) := ⟨0, hm₀_pos⟩
      have hqTop_ne : qTop ≠ q₀ := by
        intro he; have := congrArg Fin.val he; dsimp [qTop, q₀] at this; omega
      let sTop : RealExpSpace m_R m_C := embRealCoeff i₀ qTop 1
      let s₀ : RealExpSpace m_R m_C := embRealCoeff i₀ q₀ 1
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C)),
          D.card = r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ cj : RealExpSpace m_R m_C →ₗ[ℝ] ℝ, ∀ x, ψ j x = x - cj x • sTop) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          let u (m : Fin d) : RealExpSpace m_R m_C := if m = jr then sTop else ψ m s₀
          have hTu : realExpForm d m_R m_C c_R c_C w_R w_C u = w_R i₀ (c_R i₀ - 1) := by
            have hc0 : cplxTruncForm d m_C c_C w_C (fun j => (u j).2) = 0 := by
              refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun q _ => ?_
              have h0 : (u jr).2 k (q jr) = 0 := by simp [u, sTop, embRealCoeff]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) h0, mul_zero, Complex.zero_re]
            simp only [realExpForm, hc0, add_zero, realTruncForm]
            rw [Finset.sum_eq_single i₀]
            · let qTarget : Fin d → Fin (m_R i₀) := fun m => if m = jr then qTop else q₀
              have hqT_sum : ∑ m : Fin d, (qTarget m : ℕ) = c_R i₀ - 1 := by
                have hval (m : Fin d) : (qTarget m : ℕ) = if m = jr then c_R i₀ - 1 else 0 := by
                  by_cases hm : m = jr <;> simp [qTarget, hm, qTop, q₀]
                simp_rw [hval]; simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                suffices ∏ m : Fin d, (u m).1 i₀ (qTarget m) = 1 by rw [this, mul_one]
                refine Finset.prod_eq_one fun m _ => ?_
                by_cases hm : m = jr
                · subst hm; simp [u, qTarget, sTop, embRealCoeff]
                · by_cases hmr : (m : ℕ) < r
                  · obtain ⟨cm, hcm_eq⟩ := hψ_form m hmr
                    simp [u, hm, qTarget, hcm_eq, s₀, sTop, embRealCoeff,
                      singleRealCoeff_of_ne_deg i₀ qTop q₀ 1 hqTop_ne.symm]
                  · simp [u, hm, qTarget, hψ_id m hmr, s₀, embRealCoeff]
              · intro q hq hne
                have hqsum : ∑ m : Fin d, (q m : ℕ) < c_R i₀ := (Finset.mem_filter.mp hq).2
                by_cases hqjr : q jr = qTop
                · have hex : ∃ m ≠ jr, q m ≠ q₀ := by
                    by_contra h; push Not at h
                    refine hne (funext fun m => ?_)
                    by_cases hm : m = jr
                    · simp [qTarget, hm, hqjr]
                    · simp [qTarget, hm, h m hm]
                  obtain ⟨m, hm_ne, hqm_ne⟩ := hex
                  have hqm_zero : (q m : ℕ) = 0 := by
                    have hle : (q jr : ℕ) + (q m : ℕ) ≤ ∑ p : Fin d, (q p : ℕ) := by
                      rw [← Finset.add_sum_erase Finset.univ (fun p : Fin d => (q p : ℕ))
                        (Finset.mem_univ jr)]
                      exact Nat.add_le_add_left
                        (Finset.single_le_sum (f := fun p : Fin d => (q p : ℕ))
                          (fun _ _ => Nat.zero_le _)
                          (Finset.mem_erase.mpr ⟨hm_ne, Finset.mem_univ m⟩)) _
                    rw [hqjr] at hle; dsimp [qTop] at hle; omega
                  exact absurd (Fin.ext hqm_zero) hqm_ne
                · have hu0 : (u jr).1 i₀ (q jr) = 0 := by
                    simp [u, sTop, embRealCoeff,
                      singleRealCoeff_of_ne_deg i₀ qTop (q jr) 1 hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro i _ hi
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : (u jr).1 i (q jr) = 0 := by
                simp [u, sTop, embRealCoeff, singleRealCoeff_of_ne_idx i₀ qTop 1 hi]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
            · simp
          have htop_ne : w_R i₀ (c_R i₀ - 1) ≠ 0 := hwR i₀ hi₀_pos
          have hex : ∃ nr ∉ D, ℓ nr jr sTop ≠ 0 := by
            by_contra hall; push Not at hall
            have hlhs := hTu.symm.trans (hrepr u)
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (u m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hnD : n ∈ D
                · obtain ⟨m, hm, hkill⟩ := hDkill n hnD
                  have hm_ne : m ≠ jr := by intro he; subst he; simp [jr] at hm
                  refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
                  simp [u, hm_ne, hkill]
                · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [u] using hall n hnD
            rw [hrhs] at hlhs
            exact htop_ne hlhs
          obtain ⟨nr, hnr_notD, hnr⟩ := hex
          let cr : RealExpSpace m_R m_C →ₗ[ℝ] ℝ := (ℓ nr jr sTop)⁻¹ • ℓ nr jr
          let ψr : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
            LinearMap.id - cr.smulRight sTop
          have hψr_kill (x : RealExpSpace m_R m_C) : ℓ nr jr (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
            if j = jr then ψr else ψ j
          refine ⟨insert nr D, ψ', Finset.card_insert_of_notMem hnr_notD ▸ by omega, ?_, ?_, ?_⟩
          · intro j hj
            have hj_ne : j ≠ jr := by intro he; subst he; simp [jr] at hj
            simp [ψ', hj_ne, hψ_id j (by omega)]
          · intro j hj
            by_cases hjr : j = jr
            · subst hjr; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · have hlt : (j : ℕ) < r := by
                have hne : (j : ℕ) ≠ r := fun he => hjr (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjr, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
              have hjr : j ≠ jr := by intro he; subst he; simp [jr] at hj
              exact ⟨j, by omega, fun x => by simp [ψ', hjr, hkill]⟩
      obtain ⟨D, ψ, hDcard, _, hψ_form, hDkill⟩ := hpeel (d - 1) (le_refl _)
      let truncLow : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x =>
            (fun i q => if i = i₀ then if (q : ℕ) + 1 < c_R i₀ then x.1 i q else 0 else x.1 i q,
             x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : (q : ℕ) + 1 < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : (q : ℕ) + 1 < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl }
      let shiftUp : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        { toFun := fun x =>
            (fun i q =>
              if i = i₀ then
                if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ then
                  x.1 i₀ ⟨(q : ℕ) - 1, by have := hcRm i₀; omega⟩
                else 0
              else x.1 i q,
             x.2)
          map_add' := fun a b => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl
          map_smul' := fun r a => by
            ext i q
            · by_cases hi : i = i₀
              · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c_R i₀ <;> simp [hi, hq]
              · simp [hi]
            · rfl }
      let φ (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] RealExpSpace m_R m_C :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c_R' : ι_R → ℕ := Function.update c_R i₀ (c_R i₀ - 1)
      let w_R' : ι_R → ℕ → ℝ := Function.update w_R i₀ (fun m => w_R i₀ (m + 1))
      have hS' : ∑ i, c_R' i < S := by
        have h := sum_update_nat c_R i₀ (c_R i₀ - 1)
        change (∑ i, c_R' i) + c_R i₀ = (∑ i, c_R i) + (c_R i₀ - 1) at h
        omega
      have hcR'm : ∀ i, c_R' i ≤ m_R i := fun i => by
        by_cases hi : i = i₀
        · rw [hi]; simp only [c_R', Function.update_self]; have := hcRm i₀; omega
        · simp [c_R', hi, hcRm i]
      have hwR' : ∀ i, 0 < c_R' i → w_R' i (c_R' i - 1) ≠ 0 := fun i hi => by
        by_cases hi0 : i = i₀
        · subst hi0
          simp only [c_R', w_R', Function.update_self] at hi ⊢
          have : c_R i - 1 - 1 + 1 = c_R i - 1 := by omega
          rw [this]; exact hwR i hi₀_pos
        · simp only [c_R', w_R', Function.update_of_ne hi0] at hi ⊢
          exact hwR i hi
      have hφ_snd (j : Fin d) (x : RealExpSpace m_R m_C) : (φ j x).2 = x.2 := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, sTop, embRealCoeff]
      have hφ_other (j : Fin d) (i : ι_R) (hi : i ≠ i₀) (x : RealExpSpace m_R m_C)
          (q : Fin (m_R i)) :
          (φ j x).1 i q = x.1 i q := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp, hi]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, hi, sTop, embRealCoeff,
            singleRealCoeff_of_ne_idx i₀ qTop 1 hi]
      have hφ_low (j : Fin d) (hj : j ≠ jLast) (x : RealExpSpace m_R m_C) (q : Fin (m_R i₀))
          (hq : (q : ℕ) + 1 < c_R i₀) :
          (φ j x).1 i₀ q = x.1 i₀ q := by
        have hjlt : (j : ℕ) < d - 1 := by
          have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
          omega
        obtain ⟨cj, hcj⟩ := hψ_form j hjlt
        have hq_ne : q ≠ qTop := by
          intro he; have := congrArg Fin.val he; dsimp [qTop] at this; omega
        simp [φ, hj, hcj, truncLow, hq, sTop, embRealCoeff,
          singleRealCoeff_of_ne_deg i₀ qTop q 1 hq_ne]
      have hT_red (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R' w_C u =
            realExpForm d m_R m_C c_R c_C w_R w_C (fun j => φ j (u j)) := by
        simp only [realExpForm, hφ_snd]
        congr 1
        simp only [realTruncForm]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i = i₀
        · subst hi
          simp only [c_R', w_R', Function.update_self]
          have hsplit := (Finset.sum_filter_add_sum_filter_not
            (Finset.univ.filter fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i)
            (fun q : Fin d → Fin (m_R i) => 1 ≤ (q jLast : ℕ))
            (fun q => w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j))).symm
          have hzero_part :
              ∑ q ∈ (Finset.univ.filter
                  fun q : Fin d → Fin (m_R i) => ∑ j, (q j : ℕ) < c_R i).filter
                (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                w_R i (∑ j, (q j : ℕ)) * ∏ j, (φ j (u j)).1 i (q j) = 0 :=
            Finset.sum_eq_zero fun q hq => by
              have hnot1 : ¬ 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h0 : (φ jLast (u jLast)).1 i (q jLast) = 0 := by simp [φ, shiftUp, hnot1]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero]
          rw [hsplit, hzero_part, add_zero]
          let toHi (q' : Fin d → Fin (m_R i)) (j : Fin d) : Fin (m_R i) :=
            if j = jLast then
              if h : (q' jLast : ℕ) + 1 < m_R i then ⟨(q' jLast : ℕ) + 1, h⟩ else q' jLast
            else q' j
          let toLow (q : Fin d → Fin (m_R i)) (j : Fin d) : Fin (m_R i) :=
            if j = jLast then ⟨(q jLast : ℕ) - 1, by omega⟩ else q j
          have htoHi (q' : Fin d → Fin (m_R i)) (hq' : ∑ j, (q' j : ℕ) < c_R i - 1) :
              (q' jLast : ℕ) + 1 < m_R i ∧
                ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
            have hlast_lt : (q' jLast : ℕ) + 1 < m_R i := by
              have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
              have := hcRm i; omega
            refine ⟨hlast_lt, ?_⟩
            have h := sum_update_nat (fun j => (q' j : ℕ)) jLast ((q' jLast : ℕ) + 1)
            have heq : ∑ j, (toHi q' j : ℕ) =
                ∑ j, Function.update (fun m => (q' m : ℕ)) jLast ((q' jLast : ℕ) + 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toHi, hj, hlast_lt]
            rw [heq]; omega
          refine Finset.sum_nbij' toHi toLow ?_ ?_ ?_ ?_ ?_
          · intro q' hq'
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · rw [hsum_hi]; have := (Finset.mem_filter.mp hq').2; omega
            · simp [toHi, hlast_lt]
          · intro q hq
            have hq_sum : ∑ j, (q j : ℕ) < c_R i :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have h := sum_update_nat (fun j => (q j : ℕ)) jLast ((q jLast : ℕ) - 1)
            have heq : ∑ j, (toLow q j : ℕ) =
                ∑ j, Function.update (fun m => (q m : ℕ)) jLast ((q jLast : ℕ) - 1) j :=
              Finset.sum_congr rfl fun j _ => by
                by_cases hj : j = jLast <;> simp [toLow, hj]
            rw [← heq] at h
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          · intro q' hq'
            obtain ⟨hlast_lt, _⟩ := htoHi q' (Finset.mem_filter.mp hq').2
            ext j
            by_cases hj : j = jLast <;> simp [toLow, toHi, hj, hlast_lt]
          · intro q hq
            have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
            have hlt_m : (q jLast : ℕ) - 1 + 1 < m_R i := by
              have := (q jLast).2; omega
            ext j
            by_cases hj : j = jLast
            · subst hj; simp [toHi, toLow, hlt_m]; omega
            · simp [toHi, toLow, hj]
          · intro q' hq'
            have hq'_lt : ∑ j, (q' j : ℕ) < c_R i - 1 := (Finset.mem_filter.mp hq').2
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hq'_lt
            rw [hsum_hi]
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj
              have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c_R i := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                omega
              simp [toHi, hlast_lt, φ, shiftUp, hcond]
            · simp only [toHi, hj, ↓reduceIte]
              have hqj_lt : (q' j : ℕ) + 1 < c_R i := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              exact (hφ_low j hj (u j) (q' j) hqj_lt).symm
        · simp only [c_R', w_R', Function.update_of_ne hi]
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 1
          exact Finset.prod_congr rfl fun j _ => (hφ_other j i hi (u j) (q j)).symm
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : RealExpSpace m_R m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → RealExpSpace m_R m_C) :
          realExpForm d m_R m_C c_R' c_C w_R' w_C u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hD0 : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj, hkill⟩ := hDkill n hn
            have hj_ne : j ≠ jLast := by
              intro he; subst he; simp [jLast] at hj
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            simp [φ, hj_ne, hkill]
        rw [hD0, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ i, c_R' i) hS' c_R' rfl hcR'm w_R' hwR' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) + (d - 1) =
          ∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1 := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else (d - 1) * (v - 1) + 1) c_R i₀ (c_R i₀ - 1)
        change (∑ i, if c_R' i = 0 then 0 else (d - 1) * (c_R' i - 1) + 1) +
            (if c_R i₀ = 0 then 0 else (d - 1) * (c_R i₀ - 1) + 1) =
          (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) +
            (if c_R i₀ - 1 = 0 then 0 else (d - 1) * (c_R i₀ - 1 - 1) + 1) at h
        have h1 : c_R i₀ ≠ 0 := hi₀_ne
        have h2 : c_R i₀ - 1 ≠ 0 := by omega
        simp only [h1, h2, ↓reduceIte] at h
        have hmul : (d - 1) * (c_R i₀ - 1) =
            (d - 1) * (c_R i₀ - 1 - 1) + (d - 1) := by
          have hsub : c_R i₀ - 1 = (c_R i₀ - 1 - 1) + 1 := by omega
          conv_lhs => rw [hsub, mul_add, mul_one]
        omega
      omega
end KernelRank
