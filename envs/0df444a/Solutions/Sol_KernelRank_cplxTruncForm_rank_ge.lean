-- Prove2me | solution 1 for KernelRank.cplxTruncForm_rank_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:40:51.830609+00:00
-- url     : https://prove2.me/submissions/c46a92c3-1e3a-48df-bbb1-3eab33fce187

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_exists_ker_ne_zero
import Theorems.Thm_KernelRank_single_complex_rank_ge
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_of_ne_deg
import Theorems.Thm_KernelRank_singleCoeff_of_ne_idx
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
theorem _root_.solution {ι_C : Type*} [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_C : ι_C → ℕ) :
    ∀ (S : ℕ) (c : ι_C → ℕ), ∑ k, c k = S → (∀ k, c k ≤ m_C k) →
      ∀ (w : ι_C → ℕ → ℂ), (∀ k, 0 < c k → w k (c k - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (CplxExpSpace m_C →ₗ[ℝ] ℝ)),
      (∀ u, cplxTruncForm d m_C c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) ≤ R := by
  let := Classical.decEq ι_C
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro c hS hcm w hw R ℓ hrepr
    by_cases hall : ∀ k, c k = 0
    · simp [hall]
    push Not at hall
    obtain ⟨k₀, hk₀_ne⟩ := hall
    have hk₀_pos : 0 < c k₀ := Nat.pos_of_ne_zero hk₀_ne
    have hm₀_pos : 0 < m_C k₀ := lt_of_lt_of_le hk₀_pos (hcm k₀)
    have hd0 : 0 < d := by omega
    let j₀ : Fin d := ⟨0, hd0⟩
    let jLast : Fin d := ⟨d - 1, by omega⟩
    by_cases hc1 : c k₀ = 1
    · -- Case `c k₀ = 1`: peel `d` terms via `single_complex_rank_ge` and zero out block `k₀`.
      let q₀ : Fin (m_C k₀) := ⟨0, hm₀_pos⟩
      let emb0 := embCplxCoeff k₀ q₀
      let β₀ : ℂ := w k₀ 0
      have hβ₀ : β₀ ≠ 0 := by simpa [β₀, hc1] using hw k₀ hk₀_pos
      have hT_emb (z : Fin d → ℂ) :
          cplxTruncForm d m_C c w (fun j => emb0 (z j)) = (β₀ * ∏ j, z j).re := by
        simp only [cplxTruncForm]
        rw [Finset.sum_eq_single k₀]
        · rw [Finset.sum_eq_single (fun _ => q₀)]
          · simp [emb0, embCplxCoeff, β₀, q₀]
          · intro q _ hne
            have hex : ∃ j, q j ≠ q₀ := by
              by_contra h; push Not at h; exact hne (funext h)
            obtain ⟨j, hj⟩ := hex
            have h0 : emb0 (z j) k₀ (q j) = 0 :=
              singleCoeff_of_ne_deg k₀ q₀ (q j) (z j) hj
            rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, mul_zero, Complex.zero_re]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [q₀, hc1]⟩) h
        · intro k _ hk
          refine Finset.sum_eq_zero fun q _ => ?_
          have h0 : emb0 (z j₀) k (q j₀) = 0 :=
            singleCoeff_of_ne_idx k₀ q₀ (z j₀) hk (q j₀)
          rw [Finset.prod_eq_zero (Finset.mem_univ j₀) h0, mul_zero, Complex.zero_re]
        · simp
      let killC : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k => if k = k₀ then 0 else x k
          map_add' := fun a b => by ext k q; by_cases h : k = k₀ <;> simp [h]
          map_smul' := fun r a => by ext k q; by_cases h : k = k₀ <;> simp [h] }
      -- Mode `0`: find `2` distinct active terms `n₁ ≠ n₂`.
      have hex1 : ∃ n₁ : Fin R, ℓ n₁ j₀ (emb0 1) ≠ 0 := by
        by_contra h
        push Not at h
        let z (j : Fin d) : ℂ := if j = j₀ then 1 else if j = jLast then starRingEnd ℂ β₀ else 1
        have hz0 : z j₀ = 1 := by simp [z]
        have hprod_z : ∏ j : Fin d, z j = starRingEnd ℂ β₀ := by
          have hjL_ne : jLast ≠ j₀ := by
            intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
          rw [← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ jLast)]
          have her : ∏ j ∈ Finset.univ.erase jLast, z j = 1 :=
            Finset.prod_eq_one fun j hj => by
              have hne : j ≠ jLast := Finset.ne_of_mem_erase hj
              by_cases hj0 : j = j₀ <;> simp [z, hj0, hne]
          rw [her, mul_one]
          simp [z, hjL_ne]
        have hlhs := (hT_emb z).symm.trans (hrepr (fun j => emb0 (z j)))
        rw [hprod_z, Complex.mul_conj, Complex.ofReal_re] at hlhs
        have hrhs : ∑ n : Fin R, ∏ j : Fin d, ℓ n j (emb0 (z j)) = 0 :=
          Finset.sum_eq_zero fun n _ =>
            Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact h n)
        rw [hrhs] at hlhs
        exact (Complex.normSq_pos.mpr hβ₀).ne' hlhs
      obtain ⟨n₁, hn₁⟩ := hex1
      obtain ⟨w₁, hw₁_ne, hw₁_ker⟩ := exists_ker_ne_zero ((ℓ n₁ j₀).comp emb0)
      have hex2 : ∃ n₂ : Fin R, n₂ ≠ n₁ ∧ ℓ n₂ j₀ (emb0 w₁) ≠ 0 := by
        by_contra h
        push Not at h
        let z (j : Fin d) : ℂ :=
          if j = j₀ then w₁ else if j = jLast then starRingEnd ℂ (β₀ * w₁) else 1
        have hz0 : z j₀ = w₁ := by simp [z]
        have hjL_ne : jLast ≠ j₀ := by
          intro he; have := congrArg Fin.val he; dsimp [jLast, j₀] at this; omega
        have hprod_z : ∏ j : Fin d, z j = w₁ * starRingEnd ℂ (β₀ * w₁) := by
          rw [← Finset.mul_prod_erase Finset.univ z (Finset.mem_univ j₀),
            ← Finset.mul_prod_erase (Finset.univ.erase j₀) z
              (Finset.mem_erase.mpr ⟨hjL_ne, Finset.mem_univ jLast⟩)]
          have her : ∏ j ∈ (Finset.univ.erase j₀).erase jLast, z j = 1 :=
            Finset.prod_eq_one fun j hj => by
              have h1 : j ≠ jLast := (Finset.mem_erase.mp hj).1
              have h2 : j ≠ j₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
              simp [z, h1, h2]
          rw [her, mul_one]
          simp [z, hjL_ne]
        have hlhs := (hT_emb z).symm.trans (hrepr (fun j => emb0 (z j)))
        have hnorm : β₀ * (w₁ * starRingEnd ℂ (β₀ * w₁)) = Complex.normSq (β₀ * w₁) := by
          rw [← mul_assoc, Complex.mul_conj]
        rw [hprod_z, hnorm, Complex.ofReal_re] at hlhs
        have hrhs : ∑ n : Fin R, ∏ j : Fin d, ℓ n j (emb0 (z j)) = 0 :=
          Finset.sum_eq_zero fun n _ => by
            by_cases hn : n = n₁
            · subst hn
              exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact hw₁_ker)
            · exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hz0]; exact h n hn)
        rw [hrhs] at hlhs
        exact (Complex.normSq_pos.mpr (mul_ne_zero hβ₀ hw₁_ne)).ne' hlhs
      obtain ⟨n₂, hn₂₁, hn₂⟩ := hex2
      let c₁ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
        ((ℓ n₁ j₀ (emb0 1))⁻¹ • (ℓ n₁ j₀).comp killC).smulRight (1 : ℂ)
      let ψ₀a : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := killC - emb0.comp c₁
      have hψ₀a_kill1 (x : CplxExpSpace m_C) : ℓ n₁ j₀ (ψ₀a x) = 0 := by
        simp only [ψ₀a, c₁, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      let c₂ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
        ((ℓ n₂ j₀ (emb0 w₁))⁻¹ • (ℓ n₂ j₀).comp ψ₀a).smulRight w₁
      let ψ₀ : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := ψ₀a - emb0.comp c₂
      have hψ₀_kill1 (x : CplxExpSpace m_C) : ℓ n₁ j₀ (ψ₀ x) = 0 := by
        simp only [ψ₀, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, map_sub, map_smul, hψ₀a_kill1 x]
        have hw10 : ℓ n₁ j₀ (emb0 w₁) = 0 := hw₁_ker
        simp [hw10]
      have hψ₀_kill2 (x : CplxExpSpace m_C) : ℓ n₂ j₀ (ψ₀ x) = 0 := by
        simp only [ψ₀, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
        field_simp; ring
      -- Modes `1, …, d - 2`: peel `1` more term per mode via `single_complex_rank_ge`.
      have hpeel : ∀ m ≤ d - 2,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C)),
          D.card = m + 2 ∧
          (∀ j : Fin d, (j : ℕ) < m + 1 →
            ∃ cj : CplxExpSpace m_C →ₗ[ℝ] ℂ, ∀ x, ψ j x = killC x - emb0 (cj x)) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < m + 1 ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro m hm
        induction m with
        | zero =>
          refine ⟨{n₁, n₂}, fun _ => ψ₀, Finset.card_pair hn₂₁.symm, ?_, ?_⟩
          · intro j hj
            have hj0 : j = j₀ := by ext; simp [j₀]; omega
            subst hj0
            refine ⟨c₁ + c₂, fun x => ?_⟩
            simp only [ψ₀, ψ₀a, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.add_apply, map_add]
            abel
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hn'
            · exact ⟨j₀, by simp [j₀], hψ₀_kill1⟩
            · rw [Finset.mem_singleton.mp hn']
              exact ⟨j₀, by simp [j₀], hψ₀_kill2⟩
        | succ m ihm =>
          obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := ihm (by omega)
          let jm : Fin d := ⟨m + 1, by omega⟩
          have hex_next : ∃ nr ∉ D, ∃ wr : ℂ, ℓ nr jm (emb0 wr) ≠ 0 := by
            by_contra hall
            push Not at hall
            let eD : Fin D.card ≃ D := (Fintype.equivFinOfCardEq (Fintype.card_coe D)).symm
            let ℓD (p : Fin D.card) (j : Fin d) : ℂ →ₗ[ℝ] ℝ := (ℓ (eD p).1 j).comp emb0
            have hD_repr (z : Fin d → ℂ) :
                (β₀ * ∏ j, z j).re = ∑ p : Fin D.card, ∏ j, ℓD p j (z j) := by
              rw [← hT_emb, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
              have hsdiff : ∑ n ∈ Finset.univ \ D, ∏ j, ℓ n j (emb0 (z j)) = 0 :=
                Finset.sum_eq_zero fun n hn =>
                  Finset.prod_eq_zero (Finset.mem_univ jm)
                    (hall n (Finset.mem_sdiff.mp hn).2 (z jm))
              rw [hsdiff, zero_add]
              change ∑ n ∈ D, ∏ j, ℓ n j (emb0 (z j)) = _
              rw [← Finset.sum_coe_sort D]
              exact (eD.sum_comp (fun x : D => ∏ j, ℓ x.1 j (emb0 (z j)))).symm
            have hge := single_complex_rank_ge hd hβ₀ ℓD hD_repr
            omega
          obtain ⟨nr, hnr_notD, wr, hwr⟩ := hex_next
          let cr : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ nr jm (emb0 wr))⁻¹ • (ℓ nr jm).comp killC).smulRight wr
          let ψr : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := killC - emb0.comp cr
          have hψr_kill (x : CplxExpSpace m_C) : ℓ nr jm (ψr x) = 0 := by
            simp only [ψr, cr, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            if j = jm then ψr else ψ j
          refine ⟨insert nr D, ψ', Finset.card_insert_of_notMem hnr_notD ▸ by omega, ?_, ?_⟩
          · intro j hj
            by_cases hjm : j = jm
            · subst hjm; exact ⟨cr, fun x => by simp [ψ', ψr]⟩
            · have hlt : (j : ℕ) < m + 1 := by
                have hne : (j : ℕ) ≠ m + 1 := fun he => hjm (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjm, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hnD
            · exact ⟨jm, by simp [jm], fun x => by simp [ψ', hψr_kill]⟩
            · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
              have hjm : j ≠ jm := by intro he; subst he; simp [jm] at hj
              exact ⟨j, by omega, fun x => by simp [ψ', hjm, hkill]⟩
      obtain ⟨D, ψ, hDcard, hψ_form, hDkill⟩ := hpeel (d - 2) (le_refl _)
      have hD_eq : D.card = d := by omega
      let φ (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        if (j : ℕ) < d - 1 then ψ j else killC
      let c' : ι_C → ℕ := Function.update c k₀ 0
      have hS' : ∑ k, c' k < S := by
        have h := sum_update_nat c k₀ 0
        change (∑ k, c' k) + c k₀ = (∑ k, c k) + 0 at h
        omega
      have hc'm : ∀ k, c' k ≤ m_C k := fun k => by
        by_cases hk : k = k₀ <;> simp [c', hk, hcm k]
      have hwc' : ∀ k, 0 < c' k → w k (c' k - 1) ≠ 0 := fun k hk => by
        by_cases hk0 : k = k₀
        · subst hk0; simp [c'] at hk
        · simp only [c', Function.update_of_ne hk0] at hk ⊢
          exact hw k hk
      have hT_red (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w u = cplxTruncForm d m_C c w (fun j => φ j (u j)) := by
        simp only [cplxTruncForm]
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k₀),
          ← Finset.add_sum_erase Finset.univ
            (fun k => ∑ q ∈ Finset.univ.filter
                (fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k),
              (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re)
            (Finset.mem_univ k₀)]
        have hl0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_C k₀) => ∑ j, (q j : ℕ) < c' k₀),
            (w k₀ (∑ j, (q j : ℕ)) * ∏ j, u j k₀ (q j)).re = 0 := by simp [c']
        have hr0 : ∑ q ∈ Finset.univ.filter
            (fun q : Fin d → Fin (m_C k₀) => ∑ j, (q j : ℕ) < c k₀),
            (w k₀ (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k₀ (q j)).re = 0 :=
          Finset.sum_eq_zero fun q _ => by
            have hjL : ¬ (jLast : ℕ) < d - 1 := by simp [jLast]
            have h0 : φ jLast (u jLast) k₀ (q jLast) = 0 := by simp [φ, hjL, killC]
            rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero, Complex.zero_re]
        rw [hl0, hr0, zero_add, zero_add]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk_ne : k ≠ k₀ := Finset.ne_of_mem_erase hk
        simp only [c', Function.update_of_ne hk_ne]
        refine Finset.sum_congr rfl fun q _ => ?_
        congr 2
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : (j : ℕ) < d - 1
        · obtain ⟨cj, hcj⟩ := hψ_form j (by omega)
          simp [φ, hj, hcj, killC, hk_ne, emb0, embCplxCoeff,
            singleCoeff_of_ne_idx k₀ q₀ _ hk_ne]
        · simp [φ, hj, killC, hk_ne]
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
        rw [hT_red, hrepr, ← Finset.sum_sdiff (Finset.subset_univ D)]
        have hD0 : ∑ n ∈ D, ∏ j, ℓ n j (φ j (u j)) = 0 :=
          Finset.sum_eq_zero fun n hn => by
            obtain ⟨j, hj, hkill⟩ := hDkill n hn
            have hjd : (j : ℕ) < d - 1 := by omega
            refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
            simp [φ, hjd, hkill]
        rw [hD0, add_zero]
        change ∑ n ∈ rem, ∏ j, ℓ n j (φ j (u j)) = _
        rw [← Finset.sum_coe_sort rem]
        exact (eRem.sum_comp (fun x : rem => ∏ j, ℓ x.1 j (φ j (u j)))).symm
      have hle := ih (∑ k, c' k) hS' c' rfl hc'm w hwc' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) + d =
          ∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else 2 * (d - 1) * (v - 1) + d) c k₀ 0
        change (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) +
            (if c k₀ = 0 then 0 else 2 * (d - 1) * (c k₀ - 1) + d) =
          (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) + 0 at h
        simp only [hc1, one_ne_zero, ↓reduceIte, Nat.sub_self, mul_zero, zero_add, add_zero] at h
        exact h
      omega
    · -- Case `c k₀ ≥ 2`: peel `2` terms in each mode `0, …, d - 2` (`2 * (d - 1)` total),
      -- then truncate low on `0, …, d - 2` and shift up on `d - 1`.
      have hc2 : 2 ≤ c k₀ := by omega
      let qTop : Fin (m_C k₀) := ⟨c k₀ - 1, lt_of_lt_of_le (by omega) (hcm k₀)⟩
      let q₀ : Fin (m_C k₀) := ⟨0, hm₀_pos⟩
      have hqTop_ne : qTop ≠ q₀ := by
        intro he; have := congrArg Fin.val he; dsimp [qTop, q₀] at this; omega
      let embTop := embCplxCoeff k₀ qTop
      let emb0 := embCplxCoeff k₀ q₀
      let βTop : ℂ := w k₀ (c k₀ - 1)
      have hβTop : βTop ≠ 0 := hw k₀ hk₀_pos
      have hpeel : ∀ r ≤ d - 1,
          ∃ (D : Finset (Fin R)) (ψ : Fin d → (CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C)),
          D.card = 2 * r ∧
          (∀ j : Fin d, ¬ (j : ℕ) < r → ψ j = LinearMap.id) ∧
          (∀ j : Fin d, (j : ℕ) < r →
            ∃ cj : CplxExpSpace m_C →ₗ[ℝ] ℂ, ∀ x, ψ j x = x - embTop (cj x)) ∧
          (∀ n ∈ D, ∃ j : Fin d, (j : ℕ) < r ∧ ∀ x, ℓ n j (ψ j x) = 0) := by
        intro r hr
        induction r with
        | zero =>
          exact ⟨∅, fun _ => LinearMap.id, by simp, fun _ _ => rfl,
            fun _ hj => absurd hj (Nat.not_lt_zero _), by simp⟩
        | succ r ihr =>
          obtain ⟨D, ψ, hDcard, hψ_id, hψ_form, hDkill⟩ := ihr (by omega)
          let jr : Fin d := ⟨r, by omega⟩
          have hjr_ne_last : jr ≠ jLast := by
            intro he; have := congrArg Fin.val he; dsimp [jr, jLast] at this; omega
          let uOf (z : ℂ) (m : Fin d) : CplxExpSpace m_C :=
            if m = jr then embTop z
            else if m = jLast then emb0 (starRingEnd ℂ (βTop * z))
            else ψ m (emb0 1)
          have hTu (z : ℂ) :
              cplxTruncForm d m_C c w (uOf z) = Complex.normSq (βTop * z) := by
            simp only [cplxTruncForm]
            rw [Finset.sum_eq_single k₀]
            · let qTarget : Fin d → Fin (m_C k₀) := fun m => if m = jr then qTop else q₀
              have hqT_sum : ∑ m : Fin d, (qTarget m : ℕ) = c k₀ - 1 := by
                have hval (m : Fin d) : (qTarget m : ℕ) = if m = jr then c k₀ - 1 else 0 := by
                  by_cases hm : m = jr <;> simp [qTarget, hm, qTop, q₀]
                simp_rw [hval]
                simp
              rw [Finset.sum_eq_single qTarget]
              · rw [hqT_sum]
                have hprod_val : ∏ m : Fin d, uOf z m k₀ (qTarget m) =
                    z * starRingEnd ℂ (βTop * z) := by
                  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ jr),
                    ← Finset.mul_prod_erase (Finset.univ.erase jr) _
                      (Finset.mem_erase.mpr ⟨hjr_ne_last.symm, Finset.mem_univ jLast⟩)]
                  have her : ∏ m ∈ (Finset.univ.erase jr).erase jLast,
                      uOf z m k₀ (qTarget m) = 1 :=
                    Finset.prod_eq_one fun m hm => by
                      have hm_last : m ≠ jLast := (Finset.mem_erase.mp hm).1
                      have hm_jr : m ≠ jr := (Finset.mem_erase.mp (Finset.mem_erase.mp hm).2).1
                      by_cases hmr : (m : ℕ) < r
                      · obtain ⟨cm, hcm_eq⟩ := hψ_form m hmr
                        simp [uOf, hm_jr, hm_last, qTarget, hcm_eq, emb0, embTop, embCplxCoeff,
                          singleCoeff_of_ne_deg k₀ qTop q₀ _ hqTop_ne.symm]
                      · simp [uOf, hm_jr, hm_last, qTarget, hψ_id m hmr, emb0, embCplxCoeff]
                  rw [her, mul_one]
                  simp [uOf, hjr_ne_last.symm, qTarget, embTop, emb0, embCplxCoeff]
                rw [hprod_val]
                have hnorm : βTop * (z * starRingEnd ℂ (βTop * z)) = Complex.normSq (βTop * z) := by
                  rw [← mul_assoc, Complex.mul_conj]
                change (βTop * (z * starRingEnd ℂ (βTop * z))).re = _
                rw [hnorm, Complex.ofReal_re]
              · intro q hq hne
                have hqsum : ∑ m : Fin d, (q m : ℕ) < c k₀ := (Finset.mem_filter.mp hq).2
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
                · have hu0 : uOf z jr k₀ (q jr) = 0 := by
                    simp [uOf, embTop, embCplxCoeff, singleCoeff_of_ne_deg k₀ qTop (q jr) z hqjr]
                  rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero, Complex.zero_re]
              · intro h
                exact absurd (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, by rw [hqT_sum]; omega⟩) h
            · intro k _ hk
              refine Finset.sum_eq_zero fun q _ => ?_
              have hu0 : uOf z jr k (q jr) = 0 := by
                simp [uOf, embTop, embCplxCoeff, singleCoeff_of_ne_idx k₀ qTop z hk]
              rw [Finset.prod_eq_zero (Finset.mem_univ jr) hu0, mul_zero, Complex.zero_re]
            · simp
          have hD_vanish (z : ℂ) (n : Fin R) (hn : n ∈ D) :
              ∏ m : Fin d, ℓ n m (uOf z m) = 0 := by
            obtain ⟨m, hm, hkill⟩ := hDkill n hn
            have hm_jr : m ≠ jr := by intro he; subst he; simp [jr] at hm
            have hm_last : m ≠ jLast := by
              intro he; subst he; dsimp [jLast] at hm; omega
            refine Finset.prod_eq_zero (Finset.mem_univ m) ?_
            simp [uOf, hm_jr, hm_last, hkill]
          have hex1 : ∃ n₁ ∉ D, ℓ n₁ jr (embTop 1) ≠ 0 := by
            by_contra h; push Not at h
            have hlhs := (hTu 1).symm.trans (hrepr (uOf 1))
            rw [mul_one] at hlhs
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (uOf 1 m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hnD : n ∈ D
                · exact hD_vanish 1 n hnD
                · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [uOf] using h n hnD
            rw [hrhs] at hlhs
            exact (Complex.normSq_pos.mpr hβTop).ne' hlhs
          obtain ⟨n₁, hn₁_notD, hn₁⟩ := hex1
          obtain ⟨w₁, hw₁_ne, hw₁_ker⟩ := exists_ker_ne_zero ((ℓ n₁ jr).comp embTop)
          have hex2 : ∃ n₂ ∉ insert n₁ D, ℓ n₂ jr (embTop w₁) ≠ 0 := by
            by_contra h; push Not at h
            have hlhs := (hTu w₁).symm.trans (hrepr (uOf w₁))
            have hrhs : ∑ n : Fin R, ∏ m : Fin d, ℓ n m (uOf w₁ m) = 0 :=
              Finset.sum_eq_zero fun n _ => by
                by_cases hn1 : n = n₁
                · subst hn1
                  refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                  simpa [uOf] using hw₁_ker
                · by_cases hnD : n ∈ D
                  · exact hD_vanish w₁ n hnD
                  · refine Finset.prod_eq_zero (Finset.mem_univ jr) ?_
                    simpa [uOf] using h n (by simp [hn1, hnD])
            rw [hrhs] at hlhs
            exact (Complex.normSq_pos.mpr (mul_ne_zero hβTop hw₁_ne)).ne' hlhs
          obtain ⟨n₂, hn₂_not, hn₂⟩ := hex2
          let c₁ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ n₁ jr (embTop 1))⁻¹ • ℓ n₁ jr).smulRight (1 : ℂ)
          let ψa : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            LinearMap.id - embTop.comp c₁
          have hψa_kill1 (x : CplxExpSpace m_C) : ℓ n₁ jr (ψa x) = 0 := by
            simp only [ψa, c₁, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let c₂ : CplxExpSpace m_C →ₗ[ℝ] ℂ :=
            ((ℓ n₂ jr (embTop w₁))⁻¹ • (ℓ n₂ jr).comp ψa).smulRight w₁
          let ψb : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C := ψa - embTop.comp c₂
          have hψb_kill1 (x : CplxExpSpace m_C) : ℓ n₁ jr (ψb x) = 0 := by
            simp only [ψb, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, map_sub, map_smul, hψa_kill1 x]
            have hw10 : ℓ n₁ jr (embTop w₁) = 0 := hw₁_ker
            simp [hw10]
          have hψb_kill2 (x : CplxExpSpace m_C) : ℓ n₂ jr (ψb x) = 0 := by
            simp only [ψb, c₂, LinearMap.sub_apply, LinearMap.comp_apply,
              LinearMap.smulRight_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
            field_simp; ring
          let ψ' (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
            if j = jr then ψb else ψ j
          have hcard_ins : (insert n₂ (insert n₁ D)).card = 2 * (r + 1) := by
            rw [Finset.card_insert_of_notMem hn₂_not, Finset.card_insert_of_notMem hn₁_notD,
              hDcard]
            omega
          refine ⟨insert n₂ (insert n₁ D), ψ', hcard_ins, ?_, ?_, ?_⟩
          · intro j hj
            have hj_ne : j ≠ jr := by intro he; subst he; simp [jr] at hj
            simp [ψ', hj_ne, hψ_id j (by omega)]
          · intro j hj
            by_cases hjr : j = jr
            · subst hjr
              refine ⟨c₁ + c₂, fun x => ?_⟩
              simp only [ψ', ↓reduceIte, ψb, ψa, LinearMap.sub_apply, LinearMap.id_apply,
                LinearMap.comp_apply, LinearMap.add_apply, map_add]
              abel
            · have hlt : (j : ℕ) < r := by
                have hne : (j : ℕ) ≠ r := fun he => hjr (Fin.ext he)
                omega
              obtain ⟨cj, hcj⟩ := hψ_form j hlt
              exact ⟨cj, fun x => by simp [ψ', hjr, hcj]⟩
          · intro n hn
            rcases Finset.mem_insert.mp hn with rfl | hn'
            · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψb_kill2]⟩
            · rcases Finset.mem_insert.mp hn' with rfl | hnD
              · exact ⟨jr, by simp [jr], fun x => by simp [ψ', hψb_kill1]⟩
              · obtain ⟨j, hj, hkill⟩ := hDkill n hnD
                have hjr : j ≠ jr := by intro he; subst he; simp [jr] at hj
                exact ⟨j, by omega, fun x => by simp [ψ', hjr, hkill]⟩
      obtain ⟨D, ψ, hDcard, _, hψ_form, hDkill⟩ := hpeel (d - 1) (le_refl _)
      let truncLow : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k q =>
            if k = k₀ then if (q : ℕ) + 1 < c k₀ then x k q else 0 else x k q
          map_add' := fun a b => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : (q : ℕ) + 1 < c k₀ <;> simp [hk, hq]
            · simp [hk]
          map_smul' := fun r a => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : (q : ℕ) + 1 < c k₀ <;> simp [hk, hq]
            · simp [hk] }
      let shiftUp : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        { toFun := fun x k q =>
            if k = k₀ then
              if hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ then
                x k₀ ⟨(q : ℕ) - 1, by have := hcm k₀; omega⟩
              else 0
            else x k q
          map_add' := fun a b => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ <;> simp [hk, hq]
            · simp [hk]
          map_smul' := fun r a => by
            ext k q; by_cases hk : k = k₀
            · by_cases hq : 1 ≤ (q : ℕ) ∧ (q : ℕ) < c k₀ <;> simp [hk, hq]
            · simp [hk] }
      let φ (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] CplxExpSpace m_C :=
        if j = jLast then shiftUp else (ψ j).comp truncLow
      let c' : ι_C → ℕ := Function.update c k₀ (c k₀ - 1)
      let w' : ι_C → ℕ → ℂ := Function.update w k₀ (fun m => w k₀ (m + 1))
      have hS' : ∑ k, c' k < S := by
        have h := sum_update_nat c k₀ (c k₀ - 1)
        change (∑ k, c' k) + c k₀ = (∑ k, c k) + (c k₀ - 1) at h
        omega
      have hc'm : ∀ k, c' k ≤ m_C k := fun k => by
        by_cases hk : k = k₀
        · rw [hk]; simp only [c', Function.update_self]; have := hcm k₀; omega
        · simp [c', hk, hcm k]
      have hwc' : ∀ k, 0 < c' k → w' k (c' k - 1) ≠ 0 := fun k hk => by
        by_cases hk0 : k = k₀
        · subst hk0
          simp only [c', w', Function.update_self] at hk ⊢
          have : c k - 1 - 1 + 1 = c k - 1 := by omega
          rw [this]; exact hw k hk₀_pos
        · simp only [c', w', Function.update_of_ne hk0] at hk ⊢
          exact hw k hk
      have hφ_other (j : Fin d) (k : ι_C) (hk : k ≠ k₀) (x : CplxExpSpace m_C) (q : Fin (m_C k)) :
          φ j x k q = x k q := by
        by_cases hj : j = jLast
        · simp [φ, hj, shiftUp, hk]
        · have hjlt : (j : ℕ) < d - 1 := by
            have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
            omega
          obtain ⟨cj, hcj⟩ := hψ_form j hjlt
          simp [φ, hj, hcj, truncLow, hk, embTop, embCplxCoeff,
            singleCoeff_of_ne_idx k₀ qTop _ hk]
      have hφ_low (j : Fin d) (hj : j ≠ jLast) (x : CplxExpSpace m_C) (q : Fin (m_C k₀))
          (hq : (q : ℕ) + 1 < c k₀) :
          φ j x k₀ q = x k₀ q := by
        have hjlt : (j : ℕ) < d - 1 := by
          have hne : (j : ℕ) ≠ d - 1 := fun he => hj (Fin.ext he)
          omega
        obtain ⟨cj, hcj⟩ := hψ_form j hjlt
        have hq_ne : q ≠ qTop := by
          intro he; have := congrArg Fin.val he; dsimp [qTop] at this; omega
        simp [φ, hj, hcj, truncLow, hq, embTop, embCplxCoeff,
          singleCoeff_of_ne_deg k₀ qTop q _ hq_ne]
      have hT_red (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w' u = cplxTruncForm d m_C c w (fun j => φ j (u j)) := by
        simp only [cplxTruncForm]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = k₀
        · subst hk
          simp only [c', w', Function.update_self]
          have hsplit := (Finset.sum_filter_add_sum_filter_not
            (Finset.univ.filter fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k)
            (fun q : Fin d → Fin (m_C k) => 1 ≤ (q jLast : ℕ))
            (fun q => (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re)).symm
          have hzero_part :
              ∑ q ∈ (Finset.univ.filter fun q : Fin d → Fin (m_C k) => ∑ j, (q j : ℕ) < c k).filter
                (fun q => ¬ 1 ≤ (q jLast : ℕ)),
                (w k (∑ j, (q j : ℕ)) * ∏ j, φ j (u j) k (q j)).re = 0 :=
            Finset.sum_eq_zero fun q hq => by
              have hnot1 : ¬ 1 ≤ (q jLast : ℕ) := (Finset.mem_filter.mp hq).2
              have h0 : φ jLast (u jLast) k (q jLast) = 0 := by simp [φ, shiftUp, hnot1]
              rw [Finset.prod_eq_zero (Finset.mem_univ jLast) h0, mul_zero, Complex.zero_re]
          rw [hsplit, hzero_part, add_zero]
          let toHi (q' : Fin d → Fin (m_C k)) (j : Fin d) : Fin (m_C k) :=
            if j = jLast then
              if h : (q' jLast : ℕ) + 1 < m_C k then ⟨(q' jLast : ℕ) + 1, h⟩ else q' jLast
            else q' j
          let toLow (q : Fin d → Fin (m_C k)) (j : Fin d) : Fin (m_C k) :=
            if j = jLast then ⟨(q jLast : ℕ) - 1, by omega⟩ else q j
          have htoHi (q' : Fin d → Fin (m_C k)) (hq' : ∑ j, (q' j : ℕ) < c k - 1) :
              (q' jLast : ℕ) + 1 < m_C k ∧
                ∑ j, (toHi q' j : ℕ) = (∑ j, (q' j : ℕ)) + 1 := by
            have hlast_lt : (q' jLast : ℕ) + 1 < m_C k := by
              have hle := Finset.single_le_sum (f := fun j : Fin d => (q' j : ℕ))
                (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
              have := hcm k; omega
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
            have hq_sum : ∑ j, (q j : ℕ) < c k :=
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
            have hlt_m : (q jLast : ℕ) - 1 + 1 < m_C k := by
              have := (q jLast).2; omega
            ext j
            by_cases hj : j = jLast
            · subst hj; simp [toHi, toLow, hlt_m]; omega
            · simp [toHi, toLow, hj]
          · intro q' hq'
            have hq'_lt : ∑ j, (q' j : ℕ) < c k - 1 := (Finset.mem_filter.mp hq').2
            obtain ⟨hlast_lt, hsum_hi⟩ := htoHi q' hq'_lt
            rw [hsum_hi]
            congr 2
            refine Finset.prod_congr rfl fun j _ => ?_
            by_cases hj : j = jLast
            · subst hj
              have hcond : 1 ≤ (q' jLast : ℕ) + 1 ∧ (q' jLast : ℕ) + 1 < c k := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ jLast)
                omega
              simp [toHi, hlast_lt, φ, shiftUp, hcond]
            · simp only [toHi, hj, ↓reduceIte]
              have hqj_lt : (q' j : ℕ) + 1 < c k := by
                have hle := Finset.single_le_sum (f := fun m : Fin d => (q' m : ℕ))
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
                omega
              exact (hφ_low j hj (u j) (q' j) hqj_lt).symm
        · simp only [c', w', Function.update_of_ne hk]
          refine Finset.sum_congr rfl fun q _ => ?_
          congr 2
          exact Finset.prod_congr rfl fun j _ => (hφ_other j k hk (u j) (q j)).symm
      let rem : Finset (Fin R) := Finset.univ \ D
      have hcard_rem : rem.card + D.card = R := by
        simpa [rem] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
      let eRem : Fin rem.card ≃ rem := (Fintype.equivFinOfCardEq (Fintype.card_coe rem)).symm
      let ℓ' (p : Fin rem.card) (j : Fin d) : CplxExpSpace m_C →ₗ[ℝ] ℝ :=
        (ℓ (eRem p).1 j).comp (φ j)
      have hrepr' (u : Fin d → CplxExpSpace m_C) :
          cplxTruncForm d m_C c' w' u = ∑ p : Fin rem.card, ∏ j, ℓ' p j (u j) := by
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
      have hle := ih (∑ k, c' k) hS' c' rfl hc'm w' hwc' rem.card ℓ' hrepr'
      have hcost_step :
          (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) + 2 * (d - 1) =
          ∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d := by
        have h := sum_comp_update
          (fun v => if v = 0 then 0 else 2 * (d - 1) * (v - 1) + d) c k₀ (c k₀ - 1)
        change (∑ k, if c' k = 0 then 0 else 2 * (d - 1) * (c' k - 1) + d) +
            (if c k₀ = 0 then 0 else 2 * (d - 1) * (c k₀ - 1) + d) =
          (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) +
            (if c k₀ - 1 = 0 then 0 else 2 * (d - 1) * (c k₀ - 1 - 1) + d) at h
        have h1 : c k₀ ≠ 0 := hk₀_ne
        have h2 : c k₀ - 1 ≠ 0 := by omega
        simp only [h1, h2, ↓reduceIte] at h
        have hmul : 2 * (d - 1) * (c k₀ - 1) =
            2 * (d - 1) * (c k₀ - 1 - 1) + 2 * (d - 1) := by
          have hsub : c k₀ - 1 = (c k₀ - 1 - 1) + 1 := by omega
          conv_lhs => rw [hsub, mul_add, mul_one]
        omega
      omega
end KernelRank
