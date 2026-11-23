-- Prove2me | solution 1 for KernelRank.truncForm_rank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:35:55.159625+00:00
-- url     : https://prove2.me/submissions/9aa3d53b-56ad-4d61-8133-644ad42856f1

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
import Theorems.Thm_KernelRank_singleCoeff_same
import Theorems.Thm_KernelRank_singleCoeff_of_ne_idx
import Theorems.Thm_KernelRank_singleCoeff_of_ne_deg
import Theorems.Thm_KernelRank_sum_comp_update
import Theorems.Thm_KernelRank_sum_update_nat
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero


attribute [local simp] KernelRank.singleCoeff_same

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] {d : ℕ} (hd : 2 ≤ d)
    (m₀ : ι → ℕ) :
    ∀ (S : ℕ) (c : ι → ℕ), ∑ i, c i = S → (∀ i, c i ≤ m₀ i) →
      ∀ (w : ι → ℕ → ℂ), (∀ i, 0 < c i → w i (c i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → ((∀ i, Fin (m₀ i) → ℂ) →ₗ[ℂ] ℂ)),
      (∀ u, truncForm d m₀ c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c i = 0 then 0 else (d - 1) * (c i - 1) + 1) ≤ R := by
  let := Classical.decEq ι
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c hS hcm w hw R ℓ hrepr
    by_cases hall : ∀ i, c i = 0
    · simp [hall]
    push Not at hall
    obtain ⟨i₀, hi₀_ne⟩ := hall
    have hi₀_pos : 0 < c i₀ := Nat.pos_of_ne_zero hi₀_ne
    have hm₀_pos : 0 < m₀ i₀ := lt_of_lt_of_le hi₀_pos (hcm i₀)
    have hd0 : 0 < d := by omega
    by_cases hc1 : c i₀ = 1
    · -- Case `c i₀ = 1`: kill `1` term in mode `0` and zero out coordinate `i₀` in modes `j ≥ 1`.
      let q₀ : Fin (m₀ i₀) := ⟨0, hm₀_pos⟩
      let e₀ : CoeffSpace m₀ := singleCoeff i₀ q₀ 1
      have hTe : truncForm d m₀ c w (fun _ => e₀) = w i₀ 0 := by
        simp only [truncForm]
        rw [Finset.sum_eq_single i₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [e₀, q₀]
          · intro q _ hne
            have : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := this
            rw [Finset.prod_eq_zero (Finset.mem_univ j)]
            · simp
            · exact singleCoeff_of_ne_deg i₀ q₀ (q j) 1 hj
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro i _ hi
          refine Finset.sum_eq_zero fun q _ => ?_
          rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩)]
          · simp
          · exact singleCoeff_of_ne_idx i₀ q₀ 1 hi (q ⟨0, hd0⟩)
        · simp
      have hw0 : w i₀ 0 ≠ 0 := by simpa [hc1] using hw i₀ hi₀_pos
      have hsum_ne : ∑ n : Fin R, ∏ j : Fin d, ℓ n j e₀ ≠ 0 := by
        rw [← hrepr]; exact hTe ▸ hw0
      obtain ⟨n₀, _, hn₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
      have hℓ0 : ℓ n₀ ⟨0, hd0⟩ e₀ ≠ 0 := fun h =>
        hn₀ (Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩) h)
      let kill : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i => if i = i₀ then 0 else x i
          map_add' := fun a b => by
            ext i q; by_cases h : i = i₀ <;> simp [h]
          map_smul' := fun a b => by
            ext i q; by_cases h : i = i₀ <;> simp [h] }
      let φ₀ : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        kill - ((ℓ n₀ ⟨0, hd0⟩ e₀)⁻¹ • (ℓ n₀ ⟨0, hd0⟩).comp kill).smulRight e₀
      have hφ₀_kill (x : CoeffSpace m₀) : ℓ n₀ ⟨0, hd0⟩ (φ₀ x) = 0 := by
        simp only [φ₀, LinearMap.sub_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
          LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
        field_simp
        ring
      let c' : ι → ℕ := Function.update c i₀ 0
      have hS' : ∑ i, c' i < S := by
        have h := sum_update_nat c i₀ 0
        change (∑ i, c' i) + c i₀ = (∑ i, c i) + 0 at h
        omega
      have hc'm : ∀ i, c' i ≤ m₀ i := fun i => by
        by_cases h : i = i₀ <;> simp [c', h, hcm i]
      have hwc' : ∀ i, 0 < c' i → w i (c' i - 1) ≠ 0 := fun i hi => by
        have h : i ≠ i₀ := by rintro rfl; simp [c'] at hi
        simpa [c', h] using hw i (by simpa [c', h] using hi)
      let rem : Finset (Fin R) := Finset.univ.erase n₀
      have hRpos : 1 ≤ R := Fin.pos n₀
      let eRem : Fin (R - 1) ≃ rem :=
        (Fintype.equivFinOfCardEq (by simp [rem])).symm
      let φ (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        if j = ⟨0, hd0⟩ then φ₀ else kill
      let ℓ' (m : Fin (R - 1)) (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] ℂ :=
        (ℓ (eRem m).1 j).comp (φ j)
      have hrepr' (u : Fin d → CoeffSpace m₀) :
          truncForm d m₀ c' w u = ∑ m : Fin (R - 1), ∏ j, ℓ' m j (u j) := by
        have hT : truncForm d m₀ c' w u = truncForm d m₀ c w (fun j => φ j (u j)) := by
          simp only [truncForm]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = i₀
          · rw [hi]
            have hL0 : (∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m₀ i₀) => ∑ j, (q j : ℕ) < c' i₀),
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, u j i₀ (q j)) = 0 :=
              Finset.sum_eq_zero fun q hq => by
                have := (Finset.mem_filter.mp hq).2
                simp [c'] at this
            rw [hL0]
            symm
            refine Finset.sum_eq_zero fun q _ => ?_
            let j₁ : Fin d := ⟨1, hd⟩
            have hj₁ : j₁ ≠ ⟨0, hd0⟩ := by simp [j₁, Fin.ext_iff]
            have hzero : φ j₁ (u j₁) i₀ (q j₁) = 0 := by simp [φ, hj₁, kill]
            rw [Finset.prod_eq_zero (Finset.mem_univ j₁) hzero, mul_zero]
          · simp only [c', Function.update_of_ne hi]
            refine Finset.sum_congr rfl fun q _ => ?_
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = ⟨0, hd0⟩
            · subst hj
              simp [φ, φ₀, kill, hi, e₀, singleCoeff_of_ne_idx i₀ q₀ 1 hi]
            · simp [φ, hj, kill, hi]
        rw [hT, hrepr]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ n₀)]
        have hdead : (∏ j : Fin d, ℓ n₀ j (φ j (u j))) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ ⟨0, hd0⟩) (by simp [φ, hφ₀_kill])
        rw [hdead, zero_add]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hih := ih (∑ i, c' i) hS' c' rfl hc'm w hwc' (R - 1) ℓ' hrepr'
      dsimp only [c'] at hih
      have hcost := sum_comp_update (fun n => if n = 0 then 0 else (d - 1) * (n - 1) + 1) c i₀ 0
      simp only [hc1, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero, one_ne_zero] at hcost
      omega
    · -- Case `c i₀ ≥ 2`: peel `d - 1` terms in modes `0, …, d - 2` and shift mode `d - 1`.
      have hc2 : 2 ≤ c i₀ := by omega
      let q₀ : Fin (m₀ i₀) := ⟨0, hm₀_pos⟩
      let qTop : Fin (m₀ i₀) := ⟨c i₀ - 1, lt_of_lt_of_le (Nat.sub_lt hi₀_pos zero_lt_one) (hcm i₀)⟩
      let s₀ : CoeffSpace m₀ := singleCoeff i₀ q₀ 1
      let sTop : CoeffSpace m₀ := singleCoeff i₀ qTop 1
      have hqTop_ne : qTop ≠ q₀ := by
        intro h
        have := congrArg Fin.val h
        dsimp [qTop, q₀] at this
        omega
      -- Construct `r` killed indices for modes `0, …, r - 1` up to `r = d - 1`.
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀)),
          D.card = r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ c_j : CoeffSpace m₀ →ₗ[ℂ] ℂ, ∀ x, ψ j x = x - c_j x • sTop) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          let u (k : Fin d) : CoeffSpace m₀ := if k = jr then sTop else ψ k s₀
          have hTu : truncForm d m₀ c w u = w i₀ (c i₀ - 1) := by
            simp only [truncForm]
            rw [Finset.sum_eq_single i₀]
            · let qTarget : Fin d → Fin (m₀ i₀) := fun k => if k = jr then qTop else q₀
              have hqT_sum : ∑ k : Fin d, (qTarget k : ℕ) = c i₀ - 1 := by
                have hval (k : Fin d) : (qTarget k : ℕ) = if k = jr then c i₀ - 1 else 0 := by
                  by_cases hk : k = jr <;> simp [qTarget, hk, qTop, q₀]
                simp_rw [hval]
                simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                suffices ∏ k : Fin d, u k i₀ (qTarget k) = 1 by rw [this, mul_one]
                refine Finset.prod_eq_one fun k _ => ?_
                by_cases hk : k = jr
                · subst hk; simp [u, qTarget, sTop]
                · obtain ⟨ck, hck⟩ | h_id :
                    (∃ ck : CoeffSpace m₀ →ₗ[ℂ] ℂ, ∀ x, ψ k x = x - ck x • sTop) ∨
                      ψ k = LinearMap.id := by
                    by_cases hkr : (k : ℕ) < r
                    · exact Or.inl (hψ_form k hkr)
                    · exact Or.inr (hψ_id k hkr)
                  · simp [u, hk, qTarget, hck, s₀, sTop,
                      singleCoeff_of_ne_deg i₀ qTop q₀ 1 hqTop_ne.symm]
                  · simp [u, hk, qTarget, h_id, s₀]
              · intro q hq hne
                have hqsum : ∑ k : Fin d, (q k : ℕ) < c i₀ := (Finset.mem_filter.mp hq).2
                by_cases hqjr : q jr = qTop
                · have hex : ∃ k ≠ jr, q k ≠ q₀ := by
                    by_contra h; push Not at h
                    refine hne (funext fun k => ?_)
                    by_cases hk : k = jr
                    · simp [qTarget, hk, hqjr]
                    · simp [qTarget, hk, h k hk]
                  obtain ⟨k, hk_ne, hqk_ne⟩ := hex
                  have hqk_zero : (q k : ℕ) = 0 := by
                    have hle : (q jr : ℕ) + (q k : ℕ) ≤ ∑ m : Fin d, (q m : ℕ) := by
                      rw [← Finset.add_sum_erase Finset.univ (fun m : Fin d => (q m : ℕ))
                        (Finset.mem_univ jr)]
                      exact Nat.add_le_add_left
                        (Finset.single_le_sum (f := fun m : Fin d => (q m : ℕ))
                          (fun _ _ => Nat.zero_le _)
                          (Finset.mem_erase.mpr ⟨hk_ne, Finset.mem_univ k⟩)) _
                    rw [hqjr] at hle
                    dsimp [qTop] at hle
                    omega
                  exact absurd (Fin.ext hqk_zero) hqk_ne
                · have hu0 : u jr i₀ (q jr) = 0 := by
                    simp [u, sTop, singleCoeff_of_ne_deg i₀ qTop (q jr) 1 hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro i _ hi
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : u jr i (q jr) = 0 := by
                simp [u, sTop, singleCoeff_of_ne_idx i₀ qTop 1 hi]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero]
            · simp
          have hsum_sdiff : ∑ n ∈ Finset.univ \ D, ∏ k : Fin d, ℓ n k (u k) =
              w i₀ (c i₀ - 1) := by
            rw [← hTu, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
            have hD0 : ∑ n ∈ D, ∏ k : Fin d, ℓ n k (u k) = 0 :=
              Finset.sum_eq_zero fun n hn => by
                obtain ⟨j, hjr, hkill⟩ := hDkill n hn
                have hj_ne : j ≠ jr := by simp [jr, Fin.ext_iff]; omega
                exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [u, hj_ne, hkill])
            rw [hD0, add_zero]
          obtain ⟨nr, hnr_mem, hnr_prod⟩ :=
            Finset.exists_ne_zero_of_sum_ne_zero (hsum_sdiff.symm ▸ hw i₀ hi₀_pos)
          have hnr_notD : nr ∉ D := (Finset.mem_sdiff.mp hnr_mem).2
          have hℓ_top : ℓ nr jr sTop ≠ 0 := fun h =>
            hnr_prod (Finset.prod_eq_zero (Finset.mem_univ jr) (by simp [u, h]))
          let cr : CoeffSpace m₀ →ₗ[ℂ] ℂ := (ℓ nr jr sTop)⁻¹ • ℓ nr jr
          let ψr : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ := LinearMap.id - cr.smulRight sTop
          have hψr_kill (x : CoeffSpace m₀) : ℓ nr jr (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.id_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp
            ring
          let ψ' (k : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ := if k = jr then ψr else ψ k
          refine ⟨insert nr D, ψ', ?_, ?_, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem hnr_notD, hDcard]
          · intro k hk
            have hk_ne : k ≠ jr := by simp [jr, Fin.ext_iff]; omega
            simp only [ψ', hk_ne, ↓reduceIte]
            exact hψ_id k (by omega)
          · intro k hk
            by_cases hkj : k = jr
            · subst hkj; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · simp only [ψ', hkj, ↓reduceIte]
              exact hψ_form k (by simp [jr, Fin.ext_iff] at hkj; omega)
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hjr, hkill⟩ := hDkill n hnD
              have hj_ne : j ≠ jr := by simp [jr, Fin.ext_iff]; omega
              exact ⟨j, by omega, fun x => by simp [ψ', hj_ne, hkill]⟩
      obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := hpeel (d - 1) le_rfl
      let jLast : Fin d := ⟨d - 1, by omega⟩
      let truncLow : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i q => if i = i₀ then if (q : ℕ) + 1 < c i₀ then x i q else 0 else x i q
          map_add' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : (q : ℕ) + 1 < c i₀ <;> simp [hi, hq]
            · simp [hi]
          map_smul' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : (q : ℕ) + 1 < c i₀ <;> simp [hi, hq]
            · simp [hi] }
      let shiftUp : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        { toFun := fun x i q =>
            if i = i₀ then
              if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ then
                x i₀ ⟨(q : ℕ) - 1, by have := hcm i₀; omega⟩
              else 0
            else x i q
          map_add' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ <;> simp [hi, hq]
            · simp [hi]
          map_smul' := fun a b => by
            ext i q
            by_cases hi : i = i₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c i₀ <;> simp [hi, hq]
            · simp [hi] }
      let φ (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] CoeffSpace m₀ :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c' : ι → ℕ := Function.update c i₀ (c i₀ - 1)
      let w' : ι → ℕ → ℂ := Function.update w i₀ (fun k => w i₀ (k + 1))
      have hS' : ∑ i, c' i < S := by
        have h := sum_update_nat c i₀ (c i₀ - 1)
        change (∑ i, c' i) + c i₀ = (∑ i, c i) + (c i₀ - 1) at h
        omega
      have hc'm : ∀ i, c' i ≤ m₀ i := fun i => by
        by_cases h : i = i₀
        · rw [h]; simp only [c', Function.update_self]; have := hcm i₀; omega
        · simp [c', h, hcm i]
      have hwc' : ∀ i, 0 < c' i → w' i (c' i - 1) ≠ 0 := fun i hi => by
        by_cases h : i = i₀
        · rw [h]
          simp only [c', w', Function.update_self]
          have hsub : c i₀ - 1 - 1 + 1 = c i₀ - 1 := by omega
          rw [hsub]
          exact hw i₀ hi₀_pos
        · simp only [c', w', Function.update_of_ne h] at hi ⊢
          exact hw i hi
      have hdR : d - 1 ≤ R := by
        have := Finset.card_le_univ D
        simpa [hDcard] using this
      let rem : Finset (Fin R) := Finset.univ \ D
      have hrem_card : Fintype.card rem = R - (d - 1) := by
        rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ D),
          Finset.card_univ, Fintype.card_fin, hDcard]
      let eRem : Fin (R - (d - 1)) ≃ rem := (Fintype.equivFinOfCardEq hrem_card).symm
      let ℓ' (m : Fin (R - (d - 1))) (j : Fin d) : CoeffSpace m₀ →ₗ[ℂ] ℂ :=
        (ℓ (eRem m).1 j).comp (φ j)
      have hrepr' (u : Fin d → CoeffSpace m₀) :
          truncForm d m₀ c' w' u = ∑ m : Fin (R - (d - 1)), ∏ j, ℓ' m j (u j) := by
        have hT : truncForm d m₀ c' w' u = truncForm d m₀ c w (fun j => φ j (u j)) := by
          simp only [truncForm]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = i₀
          · rw [hi]
            simp only [c', w', Function.update_self]
            let S_hi := Finset.univ.filter
              (fun q : Fin d → Fin (m₀ i₀) => ∑ j, (q j : ℕ) < c i₀)
            let S_hi1 := S_hi.filter (fun q => 1 ≤ (q jLast : ℕ))
            have hdrop0 : ∑ q ∈ S_hi,
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) =
              ∑ q ∈ S_hi1,
                w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) := by
              rw [← Finset.sum_filter_add_sum_filter_not S_hi (fun q => 1 ≤ (q jLast : ℕ))]
              suffices ∑ q ∈ S_hi.filter (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                  w i₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) i₀ (q j) = 0 by
                rw [this, add_zero]
              refine Finset.sum_eq_zero fun q hq => ?_
              have hq0 : ¬ (1 ≤ (q jLast : ℕ) ∧ (q jLast : ℕ) < c i₀) :=
                fun h => (Finset.mem_filter.mp hq).2 h.1
              have hz : φ jLast (u jLast) i₀ (q jLast) = 0 := by
                simp [φ, shiftUp, hq0]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) hz, mul_zero]
            rw [hdrop0]
            let toHi (q' : Fin d → Fin (m₀ i₀)) (j : Fin d) : Fin (m₀ i₀) :=
              if h : j = jLast ∧ (q' jLast : ℕ) + 1 < m₀ i₀ then
                ⟨(q' jLast : ℕ) + 1, h.2⟩
              else q' j
            let toLow (q : Fin d → Fin (m₀ i₀)) (j : Fin d) : Fin (m₀ i₀) :=
              if j = jLast then ⟨(q jLast : ℕ) - 1, by have := (q jLast).2; omega⟩ else q j
            have htoHi (q' : Fin d → Fin (m₀ i₀))
                (hsum' : ∑ j, (q' j : ℕ) < c i₀ - 1) :
                (q' jLast : ℕ) + 1 < m₀ i₀ ∧
                  ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
              have hlast_lt : (q' jLast : ℕ) + 1 < m₀ i₀ := by
                have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                have := hcm i₀
                omega
              refine ⟨hlast_lt, ?_⟩
              have h := sum_update_nat (fun j => (q' j : ℕ)) jLast ((q' jLast : ℕ) + 1)
              have heq : ∑ j, (toHi q' j : ℕ) =
                  ∑ j, Function.update (fun k => (q' k : ℕ)) jLast ((q' jLast : ℕ) + 1) j :=
                Finset.sum_congr rfl fun j _ => by
                  by_cases hj : j = jLast <;> simp [toHi, hj, hlast_lt]
              rw [heq]
              omega
            refine Finset.sum_nbij' toHi toLow ?_ ?_ ?_ ?_ ?_
            · intro q' hq'
              obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' (Finset.mem_filter.mp hq').2
              refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
              · rw [hsum_hi]; have := (Finset.mem_filter.mp hq').2; omega
              · simp [toHi, hlast_lt]
            · intro q hq
              have hq_sum : ∑ j, (q j : ℕ) < c i₀ :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
              have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h := sum_update_nat (fun j => (q j : ℕ)) jLast ((q jLast : ℕ) - 1)
              have heq : ∑ j, (toLow q j : ℕ) =
                  ∑ j, Function.update (fun k => (q k : ℕ)) jLast ((q jLast : ℕ) - 1) j :=
                Finset.sum_congr rfl fun j _ => by
                  by_cases hj : j = jLast <;> simp [toLow, hj]
              rw [← heq] at h
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
            · intro q' hq'
              obtain ⟨hlast_lt, _⟩ := htoHi q' (Finset.mem_filter.mp hq').2
              ext j
              by_cases hj : j = jLast <;> simp [toLow, toHi, hj, hlast_lt]
            · intro q hq
              have hq_sum : ∑ j, (q j : ℕ) < c i₀ :=
                (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
              have hq_ge1 : 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have hlast_lt : (q jLast : ℕ) - 1 + 1 < m₀ i₀ := by
                have hle := Finset.single_le_sum (f := fun j : Fin d => (q j : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                have := hcm i₀
                omega
              ext j
              by_cases hj : j = jLast
              · subst hj; simp [toHi, toLow, hlast_lt]; omega
              · simp [toHi, toLow, hj]
            · intro q' hq'
              have hsum' : ∑ j, (q' j : ℕ) < c i₀ - 1 := (Finset.mem_filter.mp hq').2
              obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hsum'
              rw [hsum_hi]
              congr 1
              refine Finset.prod_congr rfl fun j _ => ?_
              have hqj_lt : (q' j : ℕ) + 1 < c i₀ := by
                have hle := Finset.single_le_sum (f := fun k : Fin d => (q' k : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              by_cases hj : j = jLast
              · subst hj
                have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c i₀ := by omega
                simp [φ, shiftUp, toHi, hlast_lt, hcond]
              · have hj_lt : (j : ℕ) < d - 1 := by
                  simp [jLast, Fin.ext_iff] at hj; omega
                obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
                have hq_ne_top : q' j ≠ qTop := by
                  intro h; have := congrArg Fin.val h; dsimp [qTop] at this; omega
                simp [φ, hj, toHi, hcj, truncLow, hqj_lt, sTop,
                  singleCoeff_of_ne_deg i₀ qTop (q' j) 1 hq_ne_top]
          · simp only [c', w', Function.update_of_ne hi]
            refine Finset.sum_congr rfl fun q _ => ?_
            congr 1
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj; simp [φ, shiftUp, hi]
            · have hj_lt : (j : ℕ) < d - 1 := by
                simp [jLast, Fin.ext_iff] at hj; omega
              obtain ⟨cj, hcj⟩ := hψ_form j hj_lt
              simp [φ, hj, hcj, truncLow, hi, sTop,
                singleCoeff_of_ne_idx i₀ qTop 1 hi]
        rw [hT, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hdead : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj_lt, hkill⟩ := hDkill n hn
            have hj_ne : j ≠ jLast := by simp [jLast, Fin.ext_iff]; omega
            exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [φ, hj_ne, hkill])
        rw [hdead, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hih := ih (∑ i, c' i) hS' c' rfl hc'm w' hwc' (R - (d - 1)) ℓ' hrepr'
      dsimp only [c'] at hih
      have hcost :=
        sum_comp_update (fun n => if n = 0 then 0 else (d - 1) * (n - 1) + 1) c i₀ (c i₀ - 1)
      have hc'_ne : c i₀ - 1 ≠ 0 := by omega
      have hmul : (d - 1) * (c i₀ - 1) = (d - 1) * (c i₀ - 1 - 1) + (d - 1) := by
        have : c i₀ - 1 = (c i₀ - 1 - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [mul_add, mul_one]
      simp only [hi₀_ne, hc'_ne, ↓reduceIte, hmul] at hcost
      omega
end KernelRank
