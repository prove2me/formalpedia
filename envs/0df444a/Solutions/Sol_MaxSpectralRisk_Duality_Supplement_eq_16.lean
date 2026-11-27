-- Prove2me | solution 1 for MaxSpectralRisk.Duality.Supplement.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:27.185477+00:00
-- url     : https://prove2.me/submissions/47721dc2-ca78-41e2-81fe-e6117bf79f63

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Finite

open MaxSpectralRisk
open MaxSpectralRisk.Duality
open MaxSpectralRisk.Duality.Supplement

/-- (16), p. 19: the full set of normalized dual extreme points is finite,
nonempty and independent of the marginals. Its minimum is attained and equals
the MES value defined from (11), for every pair of probability vectors. -/
theorem solution {m n : ℕ} (α : ℝ) (hα : 0 < α ∧ α < 1)
    (L : Fin (m + 1) → Fin (n + 1) → ℝ) :
    (vertices α L).Finite ∧ (vertices α L).Nonempty ∧
      ∀ θ ∈ (K : Set (Marginals m n)),
        ∃ z ∈ vertices α L, (∀ z' ∈ vertices α L, dualObjective z θ ≤ dualObjective z' θ) ∧
          finiteV α L θ = (dualObjective z θ : EReal) := by
            classical
            have polyFinite : ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E] [Fintype ι]
                (ℓ : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (e : E →ₗ[ℝ] ℝ),
                (({z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z} : Set E).extremePoints ℝ).Finite := by
              intro E ι _ _ _ ℓ b e
              classical
              set P : Set E := {z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z}
              apply Set.Finite.of_finite_image (f := fun z : E => fun k : ι => (ℓ k z = b k))
              · exact Set.toFinite _
              intro x hx y hy hxy
              have hxy' : ∀ k, (ℓ k x = b k ↔ ℓ k y = b k) := fun k => (congrFun hxy k).to_iff
              rw [mem_extremePoints] at hx
              have hy' := (mem_extremePoints.mp hy).1
              have hx1 := hx.1
              have hev : ∀ k, ∀ᶠ t in nhds (0:ℝ), b k ≤ ℓ k x + t * (ℓ k x - ℓ k y) := by
                intro k
                by_cases hk : ℓ k x = b k
                · have hk2 := (hxy' k).mp hk
                  exact Filter.Eventually.of_forall (fun t => by rw [hk, hk2]; simp)
                · have hlt : b k < ℓ k x := lt_of_le_of_ne (hx1.2 k) (Ne.symm hk)
                  have hc : Filter.Tendsto (fun t : ℝ => ℓ k x + t * (ℓ k x - ℓ k y)) (nhds 0) (nhds (ℓ k x)) := by
                    have hcont : Continuous (fun t : ℝ => ℓ k x + t * (ℓ k x - ℓ k y)) := by fun_prop
                    simpa using hcont.tendsto 0
                  exact (hc.eventually_const_lt hlt).mono (fun t ht => ht.le)
              obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hev)
              have hmem : ∀ t : ℝ, |t| < ε → x + t • (x - y) ∈ P := by
                intro t ht
                refine ⟨?_, ?_⟩
                · simp [map_add, map_smul, map_sub, hx1.1, hy'.1]
                · intro k
                  have := hεP (y := t) (by simpa [Real.dist_eq] using ht) k
                  simpa [map_add, map_smul, map_sub] using this
              have h1 := hmem (ε/2) (by rw [abs_of_pos (by linarith)]; linarith)
              have h2 := hmem (-(ε/2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
              have hseg : x ∈ openSegment ℝ (x + (ε/2) • (x - y)) (x + (-(ε/2)) • (x - y)) := by
                refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
                module
              have := (hx.2 _ h1 _ h2 hseg).1
              have h3 : (ε/2) • (x - y) = 0 := by
                have := congrArg (fun w => w - x) this
                simpa using this
              rcases smul_eq_zero.mp h3 with h | h
              · linarith
              · exact sub_eq_zero.mp h
            have polyBelow : ∀ {E ι : Type} [AddCommGroup E] [Module ℝ E] [Fintype ι]
                (ℓ : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (e : E →ₗ[ℝ] ℝ)
                (hpt : ∀ d, e d = 0 → (∀ k, ℓ k d = 0) → d = 0) (f : E →ₗ[ℝ] ℝ) (B : ℝ)
                (hB : ∀ w ∈ ({z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z} : Set E), B ≤ f w),
                ∀ z0 ∈ ({z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z} : Set E),
                  ∃ v ∈ ({z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z} : Set E).extremePoints ℝ, f v ≤ f z0 := by
              intro E ι _ _ _ ℓ b e hpt f B hB
              classical
              set P : Set E := {z | e z = 0 ∧ ∀ k, b k ≤ ℓ k z} with hP
              intro z0 hz0
              set act : E → ℕ := fun z => (Finset.univ.filter (fun k => ℓ k z = b k)).card with hact
              -- unbounded directions
              have hunb : ∀ z ∈ P, ∀ d, e d = 0 → (∀ k, 0 ≤ ℓ k d) → 0 ≤ f d := by
                intro z hz d hed hd
                by_contra hneg
                push Not at hneg
                set t := (f z - B + 1) / (-f d) with ht
                have htpos : 0 ≤ t := div_nonneg (by linarith [hB z hz]) (by linarith)
                have hmem : z + t • d ∈ P := by
                  refine ⟨by simp [hz.1, hed], fun k => ?_⟩
                  simp only [map_add, map_smul, smul_eq_mul]
                  nlinarith [hz.2 k, hd k]
                have := hB _ hmem
                simp only [map_add, map_smul, smul_eq_mul] at this
                have h2 : t * f d = -(f z - B + 1) := by
                  rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
                linarith
              have hdir : ∀ z ∈ P, f z ≤ f z0 → ∀ d, e d = 0 → (∀ k, ℓ k z = b k → ℓ k d = 0) → f d ≤ 0 →
                  (∃ k, ℓ k d < 0) → ∃ z' ∈ P, f z' ≤ f z0 ∧ act z < act z' := by
                intro z hz hfz d hed hact0 hfd hex
                set T := Finset.univ.filter (fun k => ℓ k d < 0)
                have hTne : T.Nonempty := by
                  obtain ⟨k, hk⟩ := hex; exact ⟨k, by simp [T, hk]⟩
                obtain ⟨k0, hk0T, hk0⟩ := Finset.exists_min_image T (fun k => (ℓ k z - b k) / (-ℓ k d)) hTne
                have hk0d : ℓ k0 d < 0 := by simpa [T] using hk0T
                set t := (ℓ k0 z - b k0) / (-ℓ k0 d) with ht
                have htpos : 0 ≤ t := div_nonneg (by linarith [hz.2 k0]) (by linarith)
                have hval : ∀ k, ℓ k (z + t • d) = ℓ k z + t * ℓ k d := by
                  intro k; simp
                refine ⟨z + t • d, ⟨by simp [hz.1, hed], fun k => ?_⟩, ?_, ?_⟩
                · rw [hval]
                  by_cases hk : ℓ k d < 0
                  · have hle := hk0 k (by simp [T, hk])
                    have : t * (-ℓ k d) ≤ ℓ k z - b k := by
                      rw [← le_div_iff₀ (by linarith)]; exact hle
                    linarith
                  · push Not at hk; nlinarith [hz.2 k]
                · simp only [map_add, map_smul, smul_eq_mul]; nlinarith
                · apply Finset.card_lt_card
                  rw [Finset.ssubset_iff_of_subset]
                  · refine ⟨k0, ?_, ?_⟩
                    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                      have hne' : (ℓ k0) d ≠ 0 := hk0d.ne
                      rw [hval, ht]; field_simp; ring
                    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                      intro h; have := hact0 k0 h; linarith
                  · intro k hk
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
                    rw [hval, hact0 k hk, hk]; ring
              by_contra hno
              push Not at hno
              have hstep : ∀ z ∈ P, f z ≤ f z0 → ∃ z' ∈ P, f z' ≤ f z0 ∧ act z < act z' := by
                intro z hz hfz
                have hne : z ∉ P.extremePoints ℝ := fun h => by have := hno z h; linarith
                rw [mem_extremePoints] at hne
                push Not at hne
                obtain ⟨z1, hz1, z2, hz2, ⟨a, c, ha, hc, hac, hseg⟩, hneq⟩ := hne hz
                set d0 := z1 - z with hd0
                have hz2eq : z2 - z = (-(a / c)) • d0 := by
                  have : z = a • z1 + c • z2 := hseg.symm
                  have hc' : c ≠ 0 := ne_of_gt hc
                  rw [hd0]
                  apply smul_right_injective E hc'
                  simp only
                  have key : a • (z1 - z) + c • (z2 - z) = 0 := by
                    calc a • (z1 - z) + c • (z2 - z) = (a • z1 + c • z2) - (a + c) • z := by module
                    _ = 0 := by rw [hseg, hac, one_smul, sub_self]
                  rw [smul_smul, mul_neg, mul_div_cancel₀ a hc']
                  linear_combination (norm := module) key
                have hd0ne : d0 ≠ 0 := by
                  intro h
                  apply hneq (sub_eq_zero.mp h)
                  rw [h, smul_zero] at hz2eq; exact sub_eq_zero.mp hz2eq
                have hed0 : e d0 = 0 := by simp [hd0, hz1.1, hz.1]
                have hact0 : ∀ k, ℓ k z = b k → ℓ k d0 = 0 := by
                  intro k hk
                  have h1 := hz1.2 k
                  have h2 := hz2.2 k
                  have : ℓ k z = a * ℓ k z1 + c * ℓ k z2 := by rw [← hseg]; simp
                  have e1 : a * (ℓ k z1 - b k) + c * (ℓ k z2 - b k) = 0 := by
                    linear_combination (-1) * this + hk - (b k) * hac
                  have p1 := mul_nonneg ha.le (sub_nonneg.mpr h1)
                  have p2 := mul_nonneg hc.le (sub_nonneg.mpr h2)
                  have h5 : a * (ℓ k z1 - b k) = 0 := by linarith
                  have hc1 : ℓ k z1 = b k := by
                    rcases mul_eq_zero.mp h5 with h | h
                    · linarith
                    · linarith
                  simp [hd0, hc1, hk]
                have hneg0 : e (-d0) = 0 := by simp [hed0]
                have hactn : ∀ k, ℓ k z = b k → ℓ k (-d0) = 0 := by
                  intro k hk; simp [hact0 k hk]
                by_cases h1 : ∃ k, ℓ k d0 < 0
                · by_cases h2 : ∃ k, 0 < ℓ k d0
                  · by_cases hf : f d0 ≤ 0
                    · exact hdir z hz hfz d0 hed0 (hact0) hf h1
                    · obtain ⟨k, hk⟩ := h2
                      exact hdir z hz hfz (-d0) hneg0 hactn (by simp; linarith) ⟨k, by simp; linarith⟩
                  · push Not at h2
                    have := hunb z hz (-d0) hneg0 (fun k => by simp; linarith [h2 k])
                    exact hdir z hz hfz d0 hed0 hact0 (by simp at this; linarith) h1
                · push Not at h1
                  by_cases h2 : ∃ k, 0 < ℓ k d0
                  · obtain ⟨k, hk⟩ := h2
                    have := hunb z hz d0 hed0 h1
                    exact hdir z hz hfz (-d0) hneg0 hactn (by simp; linarith) ⟨k, by simp; linarith⟩
                  · push Not at h2
                    exact absurd (hpt d0 hed0 (fun k => le_antisymm (h2 k) (h1 k))) hd0ne
              have hgrow : ∀ n : ℕ, ∃ z ∈ P, f z ≤ f z0 ∧ n ≤ act z := by
                intro n
                induction n with
                | zero => exact ⟨z0, hz0, le_rfl, Nat.zero_le _⟩
                | succ n ih =>
                  obtain ⟨z, hz, hfz, hn⟩ := ih
                  obtain ⟨z', hz', hfz', hlt⟩ := hstep z hz hfz
                  exact ⟨z', hz', hfz', by omega⟩
              obtain ⟨z, -, -, hn⟩ := hgrow (Fintype.card ι + 1)
              have : act z ≤ Fintype.card ι := by
                simp only [hact]; exact Finset.card_le_univ _
              omega
            let ℓ : (Fin (m + 1) × Fin (n + 1)) × Fin 3 → DualPoint m n →ₗ[ℝ] ℝ := fun k =>
              { toFun := fun z => ![(1 - α) * (z.1 k.1.1 + z.2.1 k.1.2) - z.2.2.1 k.1,
                                    z.2.2.1 k.1 + z.2.2.2, z.2.2.1 k.1] k.2
                map_add' := by
                  intro x y
                  obtain ⟨⟨i, j⟩, k⟩ := k
                  fin_cases k <;> simp <;> ring
                map_smul' := by
                  intro c x
                  obtain ⟨⟨i, j⟩, k⟩ := k
                  fin_cases k <;> simp <;> ring }
            let bb : (Fin (m + 1) × Fin (n + 1)) × Fin 3 → ℝ := fun k => ![0, L k.1.1 k.1.2, 0] k.2
            let e : DualPoint m n →ₗ[ℝ] ℝ :=
              { toFun := fun z => z.1 0
                map_add' := by intro x y; simp
                map_smul' := by intro c x; simp }
            have hPeq : dualPolyhedron α L = {z | e z = 0 ∧ ∀ k, bb k ≤ ℓ k z} := by
              ext z
              simp only [dualPolyhedron, Set.mem_ofPred_eq]
              constructor
              · rintro ⟨h0, h⟩
                refine ⟨h0, ?_⟩
                rintro ⟨⟨i, j⟩, k⟩
                fin_cases k <;> simp [ℓ, bb, (h i j).1, (h i j).2.1, (h i j).2.2]
              · rintro ⟨h0, h⟩
                refine ⟨h0, fun i j => ⟨?_, ?_, ?_⟩⟩
                · simpa [ℓ, bb] using h ((i, j), 0)
                · simpa [ℓ, bb] using h ((i, j), 1)
                · simpa [ℓ, bb] using h ((i, j), 2)
            have hpt : ∀ d, e d = 0 → (∀ k, ℓ k d = 0) → d = 0 := by
              intro d hd hk
              have h0 : ∀ i j, (1 - α) * (d.1 i + d.2.1 j) - d.2.2.1 (i, j) = 0 := fun i j => by
                simpa [ℓ] using hk ((i, j), 0)
              have h1 : ∀ i j, d.2.2.1 (i, j) + d.2.2.2 = 0 := fun i j => by
                simpa [ℓ] using hk ((i, j), 1)
              have h2 : ∀ i j, d.2.2.1 (i, j) = 0 := fun i j => by
                simpa [ℓ] using hk ((i, j), 2)
              have hd0 : d.1 0 = 0 := by simpa [e] using hd
              have hβ : d.2.2.2 = 0 := by have := h1 0 0; rw [h2] at this; linarith
              have hne : (1 - α) ≠ 0 := by linarith [hα.2]
              have hs : ∀ i j, d.1 i + d.2.1 j = 0 := fun i j => by
                have := h0 i j; rw [h2] at this
                rcases mul_eq_zero.mp (by linarith : (1 - α) * (d.1 i + d.2.1 j) = 0) with h | h
                · exact absurd h hne
                · exact h
              have hψ : ∀ j, d.2.1 j = 0 := fun j => by have := hs 0 j; rw [hd0] at this; linarith
              have hϕ : ∀ i, d.1 i = 0 := fun i => by have := hs i 0; rw [hψ] at this; linarith
              obtain ⟨d1, d2, d3, d4⟩ := d
              simp only at hϕ hψ h2 hβ
              simp only [Prod.mk_eq_zero]
              refine ⟨funext hϕ, funext hψ, funext (fun p => h2 p.1 p.2), hβ⟩
            have hfin : (vertices α L).Finite := by
              rw [vertices, hPeq]; exact polyFinite ℓ bb e
            let fθ : Marginals m n → DualPoint m n →ₗ[ℝ] ℝ := fun θ =>
              { toFun := fun z => dualObjective z θ
                map_add' := by
                  intro x y; simp only [dualObjective, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
                    Finset.sum_add_distrib]; ring
                map_smul' := by
                  intro c x; simp only [dualObjective, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
                    smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum]; ring }
            have hlow : ∀ θ ∈ (K : Set (Marginals m n)), ∀ w ∈ dualPolyhedron α L,
                (∑ i, ∑ j, θ.1 i * θ.2 j * L i j) ≤ dualObjective w θ := by
              intro θ hθ w hw
              obtain ⟨⟨h1n, h1s⟩, ⟨h2n, h2s⟩⟩ := hθ
              have hrep : dualObjective w θ = ∑ i, ∑ j, θ.1 i * θ.2 j * (w.1 i + w.2.1 j + w.2.2.2) := by
                simp only [dualObjective, mul_add, Finset.sum_add_distrib]
                have e1 : ∑ i, ∑ j, θ.1 i * θ.2 j * w.1 i = ∑ i, w.1 i * θ.1 i := by
                  refine Finset.sum_congr rfl (fun i _ => ?_)
                  rw [show (∑ j, θ.1 i * θ.2 j * w.1 i) = θ.1 i * w.1 i * ∑ j, θ.2 j by
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring), h2s]; ring
                have e2 : ∑ i, ∑ j, θ.1 i * θ.2 j * w.2.1 j = ∑ j, w.2.1 j * θ.2 j := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun j _ => ?_)
                  rw [show (∑ i, θ.1 i * θ.2 j * w.2.1 j) = θ.2 j * w.2.1 j * ∑ i, θ.1 i by
                    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring), h1s]; ring
                have e3 : ∑ i, ∑ j, θ.1 i * θ.2 j * w.2.2.2 = w.2.2.2 := by
                  rw [show (∑ i, ∑ j, θ.1 i * θ.2 j * w.2.2.2) = w.2.2.2 * ((∑ i, θ.1 i) * ∑ j, θ.2 j) by
                    rw [Finset.sum_mul, Finset.mul_sum]
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    rw [Finset.mul_sum, Finset.mul_sum]
                    exact Finset.sum_congr rfl (fun j _ => by ring), h1s, h2s]; ring
                rw [e1, e2, e3]
              rw [hrep]
              apply Finset.sum_le_sum; intro i _
              apply Finset.sum_le_sum; intro j _
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (h1n i) (h2n j))
              obtain ⟨c1, c2, c3⟩ := hw.2 i j
              nlinarith [hα.1, hα.2]
            have hbelow : ∀ θ ∈ (K : Set (Marginals m n)), ∀ w ∈ dualPolyhedron α L,
                ∃ v ∈ vertices α L, dualObjective v θ ≤ dualObjective w θ := by
              intro θ hθ w hw
              rw [vertices, hPeq]
              rw [hPeq] at hw
              have := polyBelow ℓ bb e hpt (fθ θ) _ (fun w' hw' => hlow θ hθ w' (hPeq ▸ hw')) w hw
              exact this
            -- a feasible dual point
            let R : ℝ := ∑ i, ∑ j, |L i j|
            have hLR : ∀ i j, L i j ≤ R := by
              intro i j
              calc L i j ≤ |L i j| := le_abs_self _
                _ ≤ ∑ j', |L i j'| := Finset.single_le_sum (f := fun j' => |L i j'|)
                      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
                _ ≤ R := Finset.single_le_sum (f := fun i' => ∑ j', |L i' j'|)
                      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
            have hR0 : 0 ≤ R := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
            let w0 : DualPoint m n := (0, fun _ => R / (1 - α), fun _ => R, 0)
            have hw0 : w0 ∈ dualPolyhedron α L := by
              refine ⟨rfl, fun i j => ⟨?_, ?_, ?_⟩⟩
              · simp only [w0, Pi.zero_apply, zero_add]
                rw [mul_div_cancel₀ _ (by linarith [hα.2] : (1 - α) ≠ 0)]; simp
              · simp only [w0, add_zero]; exact hLR i j
              · exact hR0
            let θ0 : Marginals m n := (Pi.single 0 1, Pi.single 0 1)
            have hθ0 : θ0 ∈ (K : Set (Marginals m n)) := by
              refine ⟨⟨fun a => ?_, by simp [θ0]⟩, ⟨fun a => ?_, by simp [θ0]⟩⟩
              · by_cases h : a = 0 <;> simp [θ0, Pi.single_apply, h]
              · by_cases h : a = 0 <;> simp [θ0, Pi.single_apply, h]
            have hne : (vertices α L).Nonempty := by
              obtain ⟨v, hv, -⟩ := hbelow θ0 hθ0 w0 hw0
              exact ⟨v, hv⟩
            refine ⟨hfin, hne, ?_⟩
            intro θ hθ
            obtain ⟨z, hz, hzmin⟩ := Set.exists_min_image (vertices α L) (fun v => dualObjective v θ) hfin hne
            have hzP : ∀ w ∈ dualPolyhedron α L, dualObjective z θ ≤ dualObjective w θ := by
              intro w hw
              obtain ⟨v, hv, hvw⟩ := hbelow θ hθ w hw
              exact (hzmin v hv).trans hvw
            refine ⟨z, hz, hzmin, ?_⟩
            have hzD : z ∈ dualPolyhedron α L := hz.1
            open MeasureTheory in
            · obtain ⟨⟨h1n, h1s⟩, ⟨h2n, h2s⟩⟩ := hθ
              have hα1 : 0 < 1 - α := by linarith [hα.2]
              set V := dualObjective z θ with hV
              let F : ((Fin (m + 1) × Fin (n + 1)) → ℝ) → ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ) → ℝ :=
                fun p y => y.2.2 + ∑ i, y.1 i * θ.1 i + ∑ j, y.2.1 j * θ.2 j +
                  ∑ k, p k * ((1 - α)⁻¹ * max (L k.1 k.2 - y.2.2) 0 - y.1 k.1 - y.2.1 k.2)
              -- Step A
              have hA : ∀ y, ∃ p ∈ stdSimplex ℝ (Fin (m + 1) × Fin (n + 1)), V ≤ F p y := by
                intro y
                obtain ⟨k0, -, hk0⟩ := Finset.exists_max_image Finset.univ
                  (fun k : Fin (m + 1) × Fin (n + 1) => (1 - α)⁻¹ * max (L k.1 k.2 - y.2.2) 0 - y.1 k.1 - y.2.1 k.2)
                  Finset.univ_nonempty
                set t := (1 - α)⁻¹ * max (L k0.1 k0.2 - y.2.2) 0 - y.1 k0.1 - y.2.1 k0.2 with ht
                refine ⟨Pi.single k0 1, ⟨fun k => ?_, ?_⟩, ?_⟩
                · by_cases h : k = k0 <;> simp [Pi.single_apply, h]
                · simp
                have hF : F (Pi.single k0 1) y = y.2.2 + ∑ i, y.1 i * θ.1 i + ∑ j, y.2.1 j * θ.2 j + t := by
                  simp only [F]
                  congr 1
                  rw [Finset.sum_eq_single k0]
                  · simp [ht]
                  · intro b _ hb; simp [Pi.single_apply, hb]
                  · simp
                rw [hF]
                set c0 := y.1 0 + t
                let w : DualPoint m n := (fun i => y.1 i + t - c0, fun j => y.2.1 j + c0,
                  fun k => max (L k.1 k.2 - y.2.2) 0, y.2.2)
                have hw : w ∈ dualPolyhedron α L := by
                  refine ⟨by simp [w, c0], fun i j => ⟨?_, ?_, ?_⟩⟩
                  · have := hk0 (i, j) (Finset.mem_univ _)
                    simp only [w]
                    have e : (1 - α) * ((1 - α)⁻¹ * max (L i j - y.2.2) 0) = max (L i j - y.2.2) 0 := by
                      field_simp
                    nlinarith
                  · simp only [w]; linarith [le_max_left (L i j - y.2.2) 0]
                  · simp only [w]; exact le_max_right _ _
                have := hzP w hw
                have hobj : dualObjective w θ = y.2.2 + ∑ i, y.1 i * θ.1 i + ∑ j, y.2.1 j * θ.2 j + t := by
                  simp only [dualObjective, w, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
                    ← Finset.mul_sum, h1s, h2s]
                  ring
                linarith
              -- quasi helpers
              have hqx : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (s : Set E), Convex ℝ s → ∀ h : E → ℝ,
                  (∀ x ∈ s, ∀ x' ∈ s, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → h (a • x + b • x') ≤ max (h x) (h x')) →
                  QuasiconvexOn ℝ s (fun x => (h x : EReal)) := by
                intro E _ _ s hs h H r x hx x' hx' a b ha hb hab
                refine ⟨hs hx.1 hx'.1 ha hb hab, ?_⟩
                calc ((h (a • x + b • x') : ℝ) : EReal) ≤ ((max (h x) (h x') : ℝ) : EReal) :=
                      EReal.coe_le_coe_iff.mpr (H x hx.1 x' hx'.1 a b ha hb hab)
                  _ ≤ r := by
                      rcases le_total (h x) (h x') with h' | h'
                      · rw [max_eq_right h']; exact hx'.2
                      · rw [max_eq_left h']; exact hx.2
              have hqv : ∀ {E : Type} [AddCommGroup E] [Module ℝ E] (s : Set E), Convex ℝ s → ∀ h : E → ℝ,
                  (∀ x ∈ s, ∀ x' ∈ s, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → min (h x) (h x') ≤ h (a • x + b • x')) →
                  QuasiconcaveOn ℝ s (fun x => (h x : EReal)) := by
                intro E _ _ s hs h H r x hx x' hx' a b ha hb hab
                refine ⟨hs hx.1 hx'.1 ha hb hab, ?_⟩
                calc r ≤ ((min (h x) (h x') : ℝ) : EReal) := by
                      rcases le_total (h x) (h x') with h' | h'
                      · rw [min_eq_left h']; exact hx.2
                      · rw [min_eq_right h']; exact hx'.2
                  _ ≤ ((h (a • x + b • x') : ℝ) : EReal) :=
                      EReal.coe_le_coe_iff.mpr (H x hx.1 x' hx'.1 a b ha hb hab)
              have hcomb : ∀ a b u v : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → a * u + b * v ≤ max u v := by
                intro a b u v ha hb hab
                have h1 := mul_le_mul_of_nonneg_left (le_max_left u v) ha
                have h2 := mul_le_mul_of_nonneg_left (le_max_right u v) hb
                have : a * max u v + b * max u v = max u v := by rw [← add_mul, hab, one_mul]
                linarith
              have hcont : ∀ y, Continuous (fun p => F p y) := by
                intro y; simp only [F]; fun_prop
              have hconty : ∀ p, Continuous (fun y => F p y) := by
                intro p; simp only [F]; fun_prop
              have hSion := Sion.minimax' (f := fun p y => ((-F p y : ℝ) : EReal))
                (X := stdSimplex ℝ (Fin (m + 1) × Fin (n + 1)))
                (Y := (Set.univ : Set ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ)))
                ⟨Pi.single (0, 0) 1, fun k => by by_cases h : k = (0, 0) <;> simp [Pi.single_apply, h], by simp⟩
                (convex_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
                (fun y _ => (continuous_coe_real_ereal.comp (hcont y).neg).continuousOn.lowerSemicontinuousOn)
                (fun y _ => hqx _ (convex_stdSimplex ℝ _) (fun p => -F p y) (by
                  intro x hx x' hx' a b ha hb hab
                  have : -F (a • x + b • x') y = a * (-F x y) + b * (-F x' y) := by
                    simp only [F, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
                      mul_assoc, ← Finset.mul_sum]
                    linear_combination (y.2.2 + ∑ i, y.1 i * θ.1 i + ∑ j, y.2.1 j * θ.2 j) * hab
                  rw [this]; exact hcomb a b _ _ ha hb hab))
                convex_univ
                (fun p _ => (continuous_coe_real_ereal.comp (hconty p).neg).continuousOn.upperSemicontinuousOn)
                (fun p hp => hqv _ convex_univ (fun y => -F p y) (by
                  intro y _ y' _ a b ha hb hab
                  have : F p (a • y + b • y') ≤ a * F p y + b * F p y' := by
                    simp only [F, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Pi.add_apply,
                      Pi.smul_apply, smul_eq_mul]
                    have hpt : ∀ k : Fin (m + 1) × Fin (n + 1), p k * ((1 - α)⁻¹ * max (L k.1 k.2 - (a * y.2.2 + b * y'.2.2)) 0
                        - (a * y.1 k.1 + b * y'.1 k.1) - (a * y.2.1 k.2 + b * y'.2.1 k.2)) ≤
                        a * (p k * ((1 - α)⁻¹ * max (L k.1 k.2 - y.2.2) 0 - y.1 k.1 - y.2.1 k.2)) +
                        b * (p k * ((1 - α)⁻¹ * max (L k.1 k.2 - y'.2.2) 0 - y'.1 k.1 - y'.2.1 k.2)) := by
                      intro k
                      have hm : max (L k.1 k.2 - (a * y.2.2 + b * y'.2.2)) 0 ≤
                          a * max (L k.1 k.2 - y.2.2) 0 + b * max (L k.1 k.2 - y'.2.2) 0 := by
                        apply max_le
                        · have eL : L k.1 k.2 = a * L k.1 k.2 + b * L k.1 k.2 := by rw [← add_mul, hab, one_mul]
                          nlinarith [mul_le_mul_of_nonneg_left (le_max_left (L k.1 k.2 - y.2.2) 0) ha,
                            mul_le_mul_of_nonneg_left (le_max_left (L k.1 k.2 - y'.2.2) 0) hb]
                        · nlinarith [le_max_right (L k.1 k.2 - y.2.2) 0, le_max_right (L k.1 k.2 - y'.2.2) 0]
                      have hpk := hp.1 k
                      have hinv : 0 ≤ (1 - α)⁻¹ := inv_nonneg.mpr hα1.le
                      have := mul_le_mul_of_nonneg_left hm (mul_nonneg hpk hinv)
                      have e : a + b = 1 := hab
                      nlinarith
                    have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hpt k)
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
                    have e1 : ∑ i, (a * y.1 i + b * y'.1 i) * θ.1 i = a * ∑ i, y.1 i * θ.1 i + b * ∑ i, y'.1 i * θ.1 i := by
                      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
                    have e2 : ∑ j, (a * y.2.1 j + b * y'.2.1 j) * θ.2 j = a * ∑ j, y.2.1 j * θ.2 j + b * ∑ j, y'.2.1 j * θ.2 j := by
                      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
                    rw [e1, e2]
                    nlinarith
                  have := hcomb a b (F p y) (F p y') ha hb hab
                  rw [min_neg_neg]; linarith))
              have hR : ⨆ y ∈ (Set.univ : Set ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ)),
                  ⨅ p ∈ stdSimplex ℝ (Fin (m + 1) × Fin (n + 1)), ((-F p y : ℝ) : EReal) ≤ ((-V : ℝ) : EReal) := by
                refine iSup₂_le fun y _ => ?_
                obtain ⟨p, hp, hVp⟩ := hA y
                exact (iInf₂_le p hp).trans (EReal.coe_le_coe_iff.mpr (by linarith))
              have hnear : ∀ ε > 0, ∃ p ∈ stdSimplex ℝ (Fin (m + 1) × Fin (n + 1)), ∀ y, V - ε < F p y := by
                intro ε hε
                have h1 : ⨅ p ∈ stdSimplex ℝ (Fin (m + 1) × Fin (n + 1)),
                    ⨆ y ∈ (Set.univ : Set ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ)), ((-F p y : ℝ) : EReal)
                    < ((-V + ε : ℝ) : EReal) := by
                  rw [hSion]; exact hR.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
                simp only [iInf_lt_iff] at h1
                obtain ⟨p, hp, hlt⟩ := h1
                refine ⟨p, hp, fun y => ?_⟩
                have := (le_iSup₂ (f := fun y (_ : y ∈ (Set.univ : Set ((Fin (m + 1) → ℝ) × (Fin (n + 1) → ℝ) × ℝ))) =>
                  ((-F p y : ℝ) : EReal)) y (Set.mem_univ y)).trans_lt hlt
                have := EReal.coe_lt_coe_iff.mp this
                linarith
              have hlin : ∀ p φ ψ b, F p (φ, ψ, b) = F p (0, 0, b) + ∑ i, φ i * (θ.1 i - ∑ j, p (i, j)) +
                  ∑ j, ψ j * (θ.2 j - ∑ i, p (i, j)) := by
                intro p φ ψ b
                simp only [F, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, mul_sub,
                  Finset.sum_sub_distrib, Finset.mul_sum]
                simp only [Fintype.sum_prod_type, mul_zero, Finset.sum_const_zero]
                have e1 : ∑ x, ∑ y, p (x, y) * φ x = ∑ x, ∑ y, φ x * p (x, y) := by simp [mul_comm]
                have e2 : ∑ x, ∑ y, p (x, y) * ψ y = ∑ y, ∑ x, ψ y * p (x, y) := by
                  rw [Finset.sum_comm]; simp [mul_comm]
                rw [e1, e2]; ring
              have hmarg : ∀ p, (∀ y, V - 1 < F p y) → (∀ i, ∑ j, p (i, j) = θ.1 i) ∧ (∀ j, ∑ i, p (i, j) = θ.2 j) := by
                intro p hp
                set C0 := F p (0, 0, 0)
                have key : ∀ (S : ℝ), 0 ≤ S → (∀ s : ℝ, V - 1 < C0 + s * S) → S = 0 := by
                  intro S hS h
                  by_contra hne
                  have hSp : 0 < S := lt_of_le_of_ne hS (Ne.symm hne)
                  have := h (-((C0 - V + 1) / S + 1))
                  have e : -((C0 - V + 1) / S + 1) * S = -(C0 - V + 1) - S := by field_simp; ring
                  linarith
                constructor
                · have hS := key (∑ i, (θ.1 i - ∑ j, p (i, j)) ^ 2) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                    (fun s => by
                      have := hp (fun i => s * (θ.1 i - ∑ j, p (i, j)), 0, 0)
                      rw [hlin] at this
                      simpa [Finset.mul_sum, mul_assoc, sq] using this)
                  intro i
                  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hS i (Finset.mem_univ _)
                  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
                  linarith
                · have hS := key (∑ j, (θ.2 j - ∑ i, p (i, j)) ^ 2) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
                    (fun s => by
                      have := hp (0, fun j => s * (θ.2 j - ∑ i, p (i, j)), 0)
                      rw [hlin] at this
                      simpa [Finset.mul_sum, mul_assoc, sq] using this)
                  intro j
                  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hS j (Finset.mem_univ _)
                  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
                  linarith
              have hint : ∀ {T : Type} [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T] (q : T → ℝ),
                  (∀ k, 0 ≤ q k) → ∀ f : T → ℝ,
                  ∫ x, f x ∂(∑ k, ENNReal.ofReal (q k) • Measure.dirac k) = ∑ k, q k * f k := by
                intro T _ _ _ q hq f
                rw [integral_finset_sum_measure (fun k _ => by
                  haveI : IsFiniteMeasure (ENNReal.ofReal (q k) • Measure.dirac k) := ⟨by simp⟩
                  exact Integrable.of_finite)]
                refine Finset.sum_congr rfl (fun k _ => ?_)
                rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq k), smul_eq_mul]
              have hle : finiteV α L θ ≤ (V : EReal) := by
                unfold finiteV Valpha
                refine iSup₂_le fun π hπ => ?_
                obtain ⟨hprob, hm1, hm2⟩ := hπ
                refine (iInf_le _ z.2.2.2).trans (EReal.coe_le_coe_iff.mpr ?_)
                simp only [MaxSpectralRisk.Duality.g]
                have hb : ∫ x, max (L x.1 x.2 - z.2.2.2) 0 ∂π ≤
                    ∫ x, (1 - α) * (z.1 x.1 + z.2.1 x.2) ∂π := by
                  apply integral_mono Integrable.of_finite Integrable.of_finite
                  intro x
                  obtain ⟨c1, c2, c3⟩ := hzD.2 x.1 x.2
                  exact max_le (by linarith) (by linarith)
                have hφ : ∫ x, z.1 x.1 ∂π = ∑ i, z.1 i * θ.1 i := by
                  have := integral_map (μ := π) (f := fun i => z.1 i) measurable_fst.aemeasurable
                    (Measurable.of_discrete).aestronglyMeasurable
                  rw [← this, hm1, vectorMeasure, hint _ h1n]
                  simp [mul_comm]
                have hψ : ∫ x, z.2.1 x.2 ∂π = ∑ j, z.2.1 j * θ.2 j := by
                  have := integral_map (μ := π) (f := fun j => z.2.1 j) measurable_snd.aemeasurable
                    (Measurable.of_discrete).aestronglyMeasurable
                  rw [← this, hm2, vectorMeasure, hint _ h2n]
                  simp [mul_comm]
                have e : ∫ x, (1 - α) * (z.1 x.1 + z.2.1 x.2) ∂π = (1 - α) * (∑ i, z.1 i * θ.1 i + ∑ j, z.2.1 j * θ.2 j) := by
                  rw [integral_const_mul, integral_add Integrable.of_finite Integrable.of_finite, hφ, hψ]
                rw [e] at hb
                have hinv : 0 ≤ (1 - α)⁻¹ := inv_nonneg.mpr hα1.le
                have := mul_le_mul_of_nonneg_left hb hinv
                rw [← mul_assoc, inv_mul_cancel₀ hα1.ne', one_mul] at this
                simp only [hV, dualObjective]
                linarith
              have hge : ∀ ε, 0 < ε → ε ≤ 1 → ((V - ε : ℝ) : EReal) ≤ finiteV α L θ := by
                intro ε hε hε1
                obtain ⟨p, hp, hFp⟩ := hnear ε hε
                obtain ⟨hr, hc⟩ := hmarg p (fun y => by linarith [hFp y])
                obtain ⟨π, hπdef⟩ : ∃ π : Measure (Fin (m + 1) × Fin (n + 1)),
                    π = ∑ k, ENNReal.ofReal (p k) • Measure.dirac k := ⟨_, rfl⟩
                have hπ : π ∈ MongeKantorovichYao.transferencePlans (vectorMeasure θ.1) (vectorMeasure θ.2) := by
                  refine ⟨⟨?_⟩, ?_, ?_⟩
                  · simp only [hπdef, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
                      smul_eq_mul, mul_one]
                    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hp.1 k), hp.2, ENNReal.ofReal_one]
                  · ext s hs
                    rw [Measure.map_apply measurable_fst hs]
                    simp only [hπdef, vectorMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
                      smul_eq_mul, Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_fst hs)]
                    rw [Fintype.sum_prod_type]
                    refine Finset.sum_congr rfl (fun i _ => ?_)
                    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
                    split_ifs with h
                    · simp only [mul_one]
                      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hp.1 _), hr i]
                    · simp
                  · ext s hs
                    rw [Measure.map_apply measurable_snd hs]
                    simp only [hπdef, vectorMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
                      smul_eq_mul, Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_snd hs)]
                    rw [Fintype.sum_prod_type, Finset.sum_comm]
                    refine Finset.sum_congr rfl (fun j _ => ?_)
                    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
                    split_ifs with h
                    · simp only [mul_one]
                      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hp.1 _), hc j]
                    · simp
                unfold finiteV Valpha
                refine le_iSup₂_of_le π hπ ?_
                refine le_iInf fun b => EReal.coe_le_coe_iff.mpr ?_
                have := hFp (0, 0, b)
                simp only [MaxSpectralRisk.Duality.g]
                rw [hπdef, hint p hp.1]
                simp only [F, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, sub_zero] at this
                rw [Finset.mul_sum]
                have e : ∑ k, p k * ((1 - α)⁻¹ * max (L k.1 k.2 - b) 0) = ∑ k, (1 - α)⁻¹ * (p k * max (L k.1 k.2 - b) 0) :=
                  Finset.sum_congr rfl (fun k _ => by ring)
                linarith
              refine le_antisymm hle ?_
              by_contra hcon
              push Not at hcon
              obtain ⟨x, hx1, hx2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
              have hx2' : x < V := EReal.coe_lt_coe_iff.mp hx2
              have := hge (min (V - x) 1) (lt_min (by linarith) one_pos) (min_le_right _ _)
              have h3 : ((x : ℝ) : EReal) ≤ ((V - min (V - x) 1 : ℝ) : EReal) :=
                EReal.coe_le_coe_iff.mpr (by linarith [min_le_left (V - x) 1])
              exact absurd (h3.trans this) (not_le.mpr hx1)
