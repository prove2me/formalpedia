-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_11
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:05:20.155043+00:00
-- url     : https://prove2.me/submissions/5a267755-e9e3-4d5a-819b-9992d803f897

import Mathlib
import Definitions.Def_MICPRep_Periodic_Setting

/- Complete task-local helper bodies from UniformApproximation.lean. -/

namespace MICPRep.Periodic.FiberBounds

/-- A denominator bound, independent of the vector being approximated. -/
theorem uniform_lattice_approx (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : Fin d → ℝ,
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ m : Fin d → ℤ,
        ‖(q : ℝ) • v - (fun i => (m i : ℝ))‖ < ε := by
  induction d generalizing ε with
  | zero =>
      refine ⟨1, by omega, fun v => ⟨1, le_rfl, le_rfl, 0, ?_⟩⟩
      rw [pi_norm_lt_iff hε]
      intro i
      exact Fin.elim0 i
  | succ d ih =>
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      let M := m + 1
      have hM : 0 < M := by dsimp [M]; omega
      have hD : 0 < (M : ℝ) + 1 := by positivity
      have hsmall : 1 / ((M : ℝ) + 1) < ε := by
        apply lt_of_le_of_lt _ hm
        apply one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
        dsimp [M]
        push_cast
        linarith
      obtain ⟨N, hN, happrox⟩ := ih (ε / ((M : ℝ) + 1)) (div_pos hε hD)
      refine ⟨M * N, Nat.mul_pos hM hN, fun v => ?_⟩
      obtain ⟨q, hq, hqN, a, ha⟩ := happrox (fun i => v i.castSucc)
      obtain ⟨k, hk, hkM, hb⟩ :=
        Real.exists_nat_abs_mul_sub_round_le ((q : ℝ) * v (Fin.last d)) hM
      refine ⟨k * q, Nat.mul_pos hk (by omega), Nat.mul_le_mul hkM hqN,
        Fin.snoc (fun i => (k : ℤ) * a i) (round ((k : ℝ) * ((q : ℝ) * v (Fin.last d)))), ?_⟩
      rw [pi_norm_lt_iff hε]
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.snoc_last,
          Nat.cast_mul, mul_assoc, Real.norm_eq_abs] using hb.trans_lt hsmall
      · have haj := (pi_norm_lt_iff (div_pos hε hD)).mp ha j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] at haj ⊢
        simp only [Fin.snoc_castSucc, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [show (k : ℝ) * q * v j.castSucc - k * (a j : ℝ) =
          (k : ℝ) * ((q : ℝ) * v j.castSucc - (a j : ℝ)) by ring,
          abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
        have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
        have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
        have hmul := mul_lt_mul_of_pos_left haj hkR
        apply hmul.trans_le
        rw [← mul_div_assoc, div_le_iff₀ hD]
        nlinarith

end MICPRep.Periodic.FiberBounds

/- Complete task-local helper bodies from ConcaveBoundedness.lean. -/

namespace MICPRep.Periodic.FiberBounds

/-- A nonnegative extended-real concave function on a convex set containing a
neighborhood of zero has finite supremum if its lattice values have finite supremum. -/
theorem bounded_on_of_lattice {d : ℕ} (A : Set (Fin d → ℝ))
    (hA : Convex ℝ A) (h0 : (0 : Fin d → ℝ) ∈ interior A)
    (W : (Fin d → ℝ) → EReal) (hW0 : ∀ x ∈ A, 0 ≤ W x)
    (hconc : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : EReal) * W x + ((1 - t : ℝ) : EReal) * W y ≤
        W (t • x + (1 - t) • y))
    (hbound : (⨆ z ∈ A ∩ intLattice d, W z) < ⊤) :
    (⨆ z ∈ A, W z) < ⊤ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  obtain ⟨N, hN, happrox⟩ := uniform_lattice_approx d (r / 2) (by linarith)
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hD : 0 < 2 * (N : ℝ) := by positivity
  let b : ℝ := (⨆ z ∈ A ∩ intLattice d, W z).toReal
  have hlattice (z : Fin d → ℝ) (hz : z ∈ A ∩ intLattice d) : W z ≤ (b : EReal) := by
    have hs : W z ≤ ⨆ u ∈ A ∩ intLattice d, W u :=
      le_iSup_of_le z (le_iSup_of_le hz le_rfl)
    exact hs.trans (EReal.le_coe_toReal (ne_of_lt hbound))
  suffices hall : ∀ x ∈ A, W x ≤ ((2 * (N : ℝ) * b : ℝ) : EReal) by
    exact lt_of_le_of_lt (iSup_le fun x => iSup_le fun hx => hall x hx) (EReal.coe_lt_top _)
  intro x hx
  obtain ⟨q, hq, hqN, m, hm⟩ := happrox ((1 / (2 * (N : ℝ))) • x)
  let t : ℝ := (q : ℝ) / (2 * (N : ℝ))
  let z : Fin d → ℝ := fun i => (m i : ℝ)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  have ht0 : 0 < t := div_pos (by linarith) hD
  have htHalf : t ≤ (1 / 2 : ℝ) := by
    dsimp [t]
    apply (div_le_iff₀ hD).mpr
    linarith
  have ht1 : 0 < 1 - t := by linarith
  have herr : ‖t • x - z‖ < r / 2 := by
    simpa only [t, z, smul_smul, div_eq_mul_inv, one_mul] using hm
  let y : Fin d → ℝ := (1 - t)⁻¹ • (z - t • x)
  have hynorm : ‖y‖ < r := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht1), mul_comm,
      ← div_eq_mul_inv]
    apply (div_lt_iff₀ ht1).mpr
    have herr' : ‖z - t • x‖ < r / 2 := by simpa only [norm_sub_rev] using herr
    have hhalf : r / 2 ≤ r * (1 - t) := by nlinarith
    exact herr'.trans_le hhalf
  have hy : y ∈ A := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hynorm)
  have hcomb : t • x + (1 - t) • y = z := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht1), one_smul]
    abel
  have hz : z ∈ A := by
    rw [← hcomb]
    exact hA hx hy ht0.le ht1.le (by ring)
  have hzint : z ∈ intLattice d := ⟨m, rfl⟩
  have hconc' := hconc x hx y hy t ht0.le (by linarith)
  rw [hcomb] at hconc'
  have hterm : 0 ≤ ((1 - t : ℝ) : EReal) * W y :=
    EReal.mul_nonneg (EReal.coe_nonneg.mpr ht1.le) (hW0 y hy)
  have hscale : (t : EReal) * W x ≤ (b : EReal) :=
    (le_add_of_nonneg_right hterm).trans (hconc'.trans (hlattice z ⟨hz, hzint⟩))
  have hxtop : W x ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_mul_top_of_pos ht0] at hscale
    exact (not_le_of_gt (EReal.coe_lt_top b)) hscale
  have hxbot : W x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hW0 x hx))
  have hxreal : ((W x).toReal : EReal) = W x := EReal.coe_toReal hxtop hxbot
  have hscaleR : t * (W x).toReal ≤ b := by
    rw [← hxreal, ← EReal.coe_mul] at hscale
    exact EReal.coe_le_coe_iff.mp hscale
  have htx : 1 ≤ (2 * (N : ℝ)) * t := by
    have hmul : (2 * (N : ℝ)) * t = q := by
      dsimp [t]
      field_simp
    rw [hmul]
    exact hqR
  have hw0 : 0 ≤ (W x).toReal := EReal.toReal_nonneg (hW0 x hx)
  have hlarge := mul_le_mul_of_nonneg_left hscaleR hD.le
  have hsmall := mul_le_mul_of_nonneg_right htx hw0
  rw [← hxreal]
  apply EReal.coe_le_coe_iff.mpr
  nlinarith

end MICPRep.Periodic.FiberBounds

/- Complete task-local helper bodies from AffineCoordinates.lean. -/

namespace MICPRep.Periodic.FiberBounds

lemma affZ_direction_integer_span {d : ℕ} (I : Set (Fin d → ℝ)) :
    (affZ I).direction =
      Submodule.span ℝ (((affZ I).direction : Set (Fin d → ℝ)) ∩ intLattice d) := by
  apply le_antisymm
  · change (affineSpan ℝ (I ∩ intLattice d)).direction ≤ _
    rw [direction_affineSpan, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, y, hy, rfl⟩
    apply Submodule.subset_span
    refine ⟨AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hx)
      (subset_affineSpan ℝ _ hy), ?_⟩
    rcases hx.2 with ⟨a, rfl⟩
    rcases hy.2 with ⟨b, rfl⟩
    refine ⟨a - b, ?_⟩
    ext i
    simp
  · exact Submodule.span_le.mpr fun _ hx => hx.1

/-- Integer generators give continuous affine coordinates; independence is unnecessary. -/
lemma integer_affine_coordinates {d : ℕ} (I : Set (Fin d → ℝ))
    {z : Fin d → ℝ} (hz : z ∈ intrinsicInterior ℝ (IZ I)) (hzZ : z ∈ intLattice d) :
    ∃ (k : ℕ) (L : (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ)),
      (∀ x, L x + z ∈ affZ I) ∧
      (∀ y ∈ IZ I, ∃ x, L x + z = y) ∧
      (∀ x ∈ intLattice k, L x + z ∈ intLattice d) ∧
      (0 : Fin k → ℝ) ∈ interior ((fun x => L x + z) ⁻¹' IZ I) := by
  classical
  have hzI : z ∈ IZ I := intrinsicInterior_subset hz
  let D : Set (Fin d → ℝ) := ((affZ I).direction : Set (Fin d → ℝ)) ∩ intLattice d
  obtain ⟨v, hv, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ D
  let k := Module.finrank ℝ (Submodule.span ℝ D)
  let L : (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Fintype.linearCombination ℝ v
  have hL : L.range = (affZ I).direction := by
    rw [Fintype.range_linearCombination, hspan]
    exact (affZ_direction_integer_span I).symm
  have hmem : ∀ x, L x + z ∈ affZ I := by
    intro x
    apply AffineSubspace.vadd_mem_of_mem_direction _ hzI.2
    rw [← hL]
    exact ⟨x, rfl⟩
  refine ⟨k, L, hmem, ?_, ?_, ?_⟩
  · intro y hy
    have hdir : y - z ∈ (affZ I).direction :=
      AffineSubspace.vsub_mem_direction hy.2 hzI.2
    rw [← hL] at hdir
    obtain ⟨x, hx⟩ := hdir
    exact ⟨x, by rw [hx]; abel⟩
  · rintro x ⟨a, rfl⟩
    choose b hb using fun i => (hv i).2
    rcases hzZ with ⟨c, rfl⟩
    refine ⟨fun j => (∑ i, a i * b i j) + c j, ?_⟩
    ext j
    simp only [L, Fintype.linearCombination_apply, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_sum, Int.cast_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hb i]
  · have hF : affZ I = affineSpan ℝ (IZ I) := by
      apply le_antisymm
      · apply affineSpan_mono ℝ
        intro y hy
        exact ⟨hy.1, subset_affineSpan ℝ _ hy⟩
      · exact affineSpan_le.mpr Set.inter_subset_right
    let ψ : (Fin k → ℝ) → affineSpan ℝ (IZ I) :=
      fun x => ⟨L x + z, hF ▸ hmem x⟩
    have hψ : Continuous ψ :=
      (L.continuous_of_finiteDimensional.add continuous_const).subtype_mk _
    obtain ⟨z', hz', hz'eq⟩ := mem_intrinsicInterior.mp hz
    have hzero : ψ 0 = z' := by
      apply Subtype.ext
      simpa [ψ] using hz'eq.symm
    have hpre : (0 : Fin k → ℝ) ∈ ψ ⁻¹' interior ((↑) ⁻¹' IZ I) := by
      change ψ 0 ∈ interior ((fun a : affineSpan ℝ (IZ I) => (a : Fin d → ℝ)) ⁻¹' IZ I)
      rw [hzero]
      exact hz'
    exact preimage_interior_subset_interior_preimage hψ hpre

end MICPRep.Periodic.FiberBounds

/- Complete task-local helper bodies from SupportConcavity.lean. -/

namespace MICPRep.Periodic.FiberBounds

lemma continuous_real_mul (a : ℝ) : Continuous (fun x : EReal => (a : EReal) * x) := by
  by_cases ha : a = 0
  · simpa [ha] using (continuous_const : Continuous (fun _ : EReal => (0 : EReal)))
  · apply continuous_iff_continuousAt.mpr
    intro x
    exact (EReal.continuousAt_mul (p := ((a : EReal), x)) (.inl (by change (a : EReal) ≠ 0; exact_mod_cast ha))
      (.inl (by change (a : EReal) ≠ 0; exact_mod_cast ha)) (.inl (EReal.coe_ne_bot a))
      (.inl (EReal.coe_ne_top a))).comp
        (continuousAt_const.prodMk continuousAt_id)

lemma real_mul_iSup {ι : Type*} [Nonempty ι] (u : ι → EReal) (a : ℝ) (ha : 0 ≤ a) :
    (a : EReal) * (⨆ i, u i) = ⨆ i, (a : EReal) * u i :=
  Monotone.map_ciSup_of_continuousAt (continuous_real_mul a).continuousAt
    (fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast ha))

lemma coe_iSup_ne_bot {ι : Type*} [Nonempty ι] (u : ι → ℝ) :
    (⨆ i, (u i : EReal)) ≠ ⊥ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ne_of_gt ((EReal.bot_lt_coe (u i)).trans_le (le_iSup (fun i => (u i : EReal)) i))

lemma coe_iSup_add {ι κ : Type*} [Nonempty ι] [Nonempty κ] (u : ι → ℝ) (v : κ → ℝ) :
    (⨆ i, (u i : EReal)) + (⨆ j, (v j : EReal)) = ⨆ i, ⨆ j, ((u i + v j : ℝ) : EReal) := by
  have hleft : ContinuousAt (fun x : EReal => x + ⨆ j, (v j : EReal))
      (⨆ i, (u i : EReal)) :=
    (EReal.continuousAt_add (.inr (coe_iSup_ne_bot v)) (.inl (coe_iSup_ne_bot u))).comp
      (continuousAt_id.prodMk continuousAt_const)
  rw [Monotone.map_ciSup_of_continuousAt hleft (fun _ _ h => add_le_add h le_rfl)]
  congr 1
  funext i
  have hright : ContinuousAt (fun x : EReal => (u i : EReal) + x)
      (⨆ j, (v j : EReal)) :=
    (EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))).comp
      (continuousAt_const.prodMk continuousAt_id)
  simpa only [EReal.coe_add] using
    Monotone.map_ciSup_of_continuousAt hright (fun _ _ h => add_le_add le_rfl h)

lemma weighted_iSup_le {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    (u : ι → ℝ) (v : κ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (H : EReal)
    (h : ∀ i j, ((a * u i + b * v j : ℝ) : EReal) ≤ H) :
    (a : EReal) * (⨆ i, (u i : EReal)) +
      (b : EReal) * (⨆ j, (v j : EReal)) ≤ H := by
  rw [real_mul_iSup _ a ha, real_mul_iSup _ b hb]
  simp only [← EReal.coe_mul]
  rw [coe_iSup_add]
  exact iSup_le fun i => iSup_le fun j => h i j

lemma fiber_nonempty {n p d : ℕ} {M : Set (Ambient n p d)} {z : Fin d → ℝ}
    (hz : z ∈ indexSet M) : (zProj M z).Nonempty := by
  rcases hz with ⟨⟨x, y, z⟩, h, rfl⟩
  exact ⟨x, y, h⟩

lemma fiber_combo {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M)
    {z₁ z₂ : Fin d → ℝ} {x₁ x₂ : Pt n} (hx₁ : x₁ ∈ zProj M z₁)
    (hx₂ : x₂ ∈ zProj M z₂) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • x₁ + (1 - t) • x₂ ∈ zProj M (t • z₁ + (1 - t) • z₂) := by
  obtain ⟨y₁, hy₁⟩ := hx₁
  obtain ⟨y₂, hy₂⟩ := hx₂
  exact ⟨t • y₁ + (1 - t) • y₂,
    hM hy₁ hy₂ ht (sub_nonneg.mpr ht1) (by ring)⟩

lemma support_concave {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M)
    (c : Pt n) {z₁ z₂ : Fin d → ℝ} (hz₁ : z₁ ∈ indexSet M)
    (hz₂ : z₂ ∈ indexSet M) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : EReal) * supportFn (zProj M z₁) c +
      ((1 - t : ℝ) : EReal) * supportFn (zProj M z₂) c ≤
        supportFn (zProj M (t • z₁ + (1 - t) • z₂)) c := by
  classical
  let : Nonempty (zProj M z₁) := (fiber_nonempty hz₁).to_subtype
  let : Nonempty (zProj M z₂) := (fiber_nonempty hz₂).to_subtype
  unfold supportFn
  rw [← iSup_subtype'', ← iSup_subtype'']
  apply weighted_iSup_le _ _ t (1 - t) ht (sub_nonneg.mpr ht1)
  intro x y
  have hxy := fiber_combo hM x.property y.property ht ht1
  have h : ((inner ℝ c (t • x.val + (1 - t) • y.val) : ℝ) : EReal) ≤
      ⨆ x ∈ zProj M (t • z₁ + (1 - t) • z₂), ((inner ℝ c x : ℝ) : EReal) :=
    le_iSup_of_le _ (le_iSup_of_le hxy le_rfl)
  simpa only [inner_add_right, inner_smul_right] using h

lemma support_ne_bot {n : ℕ} {A : Set (Pt n)} (hA : A.Nonempty) (c : Pt n) :
    supportFn A c ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hA
  exact ne_of_gt ((EReal.bot_lt_coe (inner ℝ c x)).trans_le
    (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))

lemma real_mul_ne_bot {a : ℝ} (ha : 0 ≤ a) {x : EReal} (hx : x ≠ ⊥) :
    (a : EReal) * x ≠ ⊥ :=
  (EReal.mul_ne_bot _ _).mpr ⟨.inl (EReal.coe_ne_bot a), .inr hx,
    .inl (EReal.coe_ne_top a), .inl (by exact_mod_cast ha)⟩

lemma lower_support_convex {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M)
    (c : Pt n) {z₁ z₂ : Fin d → ℝ} (hz₁ : z₁ ∈ indexSet M)
    (hz₂ : z₂ ∈ indexSet M) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -supportFn (zProj M (t • z₁ + (1 - t) • z₂)) (-c) ≤
      (t : EReal) * (-supportFn (zProj M z₁) (-c)) +
      ((1 - t : ℝ) : EReal) * (-supportFn (zProj M z₂) (-c)) := by
  have h := EReal.neg_le_neg_iff.mpr (support_concave hM (-c) hz₁ hz₂ ht ht1)
  rw [EReal.neg_add (.inl (real_mul_ne_bot ht (support_ne_bot (fiber_nonempty hz₁) (-c))))
    (.inr (real_mul_ne_bot (sub_nonneg.mpr ht1) (support_ne_bot (fiber_nonempty hz₂) (-c)))),
    sub_eq_add_neg] at h
  simpa only [sub_eq_add_neg, mul_neg] using h

lemma width_nonneg {n : ℕ} {A : Set (Pt n)} (hA : A.Nonempty) (c : Pt n) :
    0 ≤ supportFn A c + supportFn A (-c) := by
  obtain ⟨x, hx⟩ := hA
  have h₁ : ((inner ℝ c x : ℝ) : EReal) ≤ supportFn A c :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have h₂ : ((inner ℝ (-c) x : ℝ) : EReal) ≤ supportFn A (-c) :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have h := add_le_add h₁ h₂
  simpa only [inner_neg_left, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero] using h

lemma width_concave {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M)
    (c : Pt n) {z₁ z₂ : Fin d → ℝ} (hz₁ : z₁ ∈ indexSet M)
    (hz₂ : z₂ ∈ indexSet M) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : EReal) * (supportFn (zProj M z₁) c + supportFn (zProj M z₁) (-c)) +
      ((1 - t : ℝ) : EReal) * (supportFn (zProj M z₂) c + supportFn (zProj M z₂) (-c)) ≤
        supportFn (zProj M (t • z₁ + (1 - t) • z₂)) c +
        supportFn (zProj M (t • z₁ + (1 - t) • z₂)) (-c) := by
  have h := add_le_add (support_concave hM c hz₁ hz₂ ht ht1)
    (support_concave hM (-c) hz₁ hz₂ ht ht1)
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast ht) (EReal.coe_ne_top _),
    EReal.left_distrib_of_nonneg_of_ne_top
      (by exact_mod_cast sub_nonneg.mpr ht1) (EReal.coe_ne_top _)]
  simpa only [add_assoc, add_left_comm, add_comm] using h

lemma index_convex {n p d : ℕ} {M : Set (Ambient n p d)} (hM : Convex ℝ M) :
    Convex ℝ (indexSet M) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rcases hz₁ with ⟨v₁, hv₁, rfl⟩
  rcases hz₂ with ⟨v₂, hv₂, rfl⟩
  exact ⟨a • v₁ + b • v₂, hM hv₁ hv₂ ha hb hab, rfl⟩

end MICPRep.Periodic.FiberBounds


namespace MICPRep.Periodic.FiberBounds

lemma bounded_on_IZ {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (W : (Fin d → ℝ) → EReal) (hW0 : ∀ x ∈ I, 0 ≤ W x)
    (hconc : ∀ x ∈ I, ∀ y ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (t : EReal) * W x + ((1 - t : ℝ) : EReal) * W y ≤
        W (t • x + (1 - t) • y))
    (hint : (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty) :
    (⨆ z ∈ IZ I ∩ intLattice d, W z) < ⊤ ↔ (⨆ z ∈ IZ I, W z) < ⊤ := by
  constructor
  · intro hb
    obtain ⟨z, hz, hzZ⟩ := hint
    obtain ⟨k, L, _, hsurj, hlat, hzero⟩ := integer_affine_coordinates I hz hzZ
    let A := (fun x => L x + z) ⁻¹' IZ I
    have heq (x y : Fin k → ℝ) (a b : ℝ) (hab : a + b = 1) :
        L (a • x + b • y) + z = a • (L x + z) + b • (L y + z) := by
      rw [map_add, map_smul, map_smul, smul_add, smul_add, add_add_add_comm,
        ← add_smul, hab, one_smul]
    have hA : Convex ℝ A := by
      intro x hx y hy a b ha hb hab
      change L (a • x + b • y) + z ∈ IZ I
      rw [heq _ _ _ _ hab]
      exact (hI.inter (affZ I).convex) hx hy ha hb hab
    have hW : (⨆ x ∈ A, W (L x + z)) < ⊤ := by
      apply bounded_on_of_lattice A hA hzero (fun x => W (L x + z))
      · exact fun x hx => hW0 _ hx.1
      · intro x hx y hy t ht ht1
        rw [heq _ _ _ _ (by ring)]
        exact hconc _ hx.1 _ hy.1 t ht ht1
      · apply lt_of_le_of_lt _ hb
        apply iSup_le
        intro x
        apply iSup_le
        intro hx
        exact le_iSup_of_le (L x + z) (le_iSup_of_le ⟨hx.1, hlat x hx.2⟩ le_rfl)
    apply lt_of_le_of_lt _ hW
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    obtain ⟨x, rfl⟩ := hsurj y hy
    exact le_iSup_of_le x (le_iSup_of_le hy le_rfl)
  · intro hb
    apply lt_of_le_of_lt _ hb
    exact iSup_le fun z => iSup_le fun hz => le_iSup_of_le z (le_iSup_of_le hz.1 le_rfl)

end MICPRep.Periodic.FiberBounds

open MICPRep.Periodic MICPRep.Periodic.FiberBounds
open scoped ENNReal Matrix

theorem solution {n p d : ℕ} (M : Set (Ambient n p d)) (S : Set (Pt n))
    (hM : Induces M S) :
    let I := indexSet M
    let f : Pt n → (Fin d → ℝ) → EReal := fun c z => -supportFn (zProj M z) (-c)
    let g : Pt n → (Fin d → ℝ) → EReal := fun c z => supportFn (zProj M z) c
    let w : Pt n → (Fin d → ℝ) → EReal := fun c z => g c z - f c z
    (∀ c : Pt n, ∀ z₁ ∈ I, ∀ z₂ ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        f c (t • z₁ + (1 - t) • z₂) ≤ (t : EReal) * f c z₁ + ((1 - t : ℝ) : EReal) * f c z₂ ∧
        (t : EReal) * g c z₁ + ((1 - t : ℝ) : EReal) * g c z₂ ≤ g c (t • z₁ + (1 - t) • z₂) ∧
        (t : EReal) * w c z₁ + ((1 - t : ℝ) : EReal) * w c z₂ ≤ w c (t • z₁ + (1 - t) • z₂)) ∧
    (∀ c : Pt n, ∀ z ∈ I, f c z < ⊤ ∧ ⊥ < g c z ∧ 0 ≤ w c z) ∧
    ((intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty →
      ∀ c : Pt n, ((⨆ z ∈ IZ I ∩ intLattice d, w c z) < ⊤ ↔ (⨆ z ∈ IZ I, w c z) < ⊤)) := by
  dsimp only
  simp only [sub_eq_add_neg, neg_neg]
  refine ⟨?_, ?_, ?_⟩
  · intro c z₁ hz₁ z₂ hz₂ t ht ht1
    exact ⟨lower_support_convex hM.2.1 c hz₁ hz₂ ht ht1,
      support_concave hM.2.1 c hz₁ hz₂ ht ht1,
      width_concave hM.2.1 c hz₁ hz₂ ht ht1⟩
  · intro c z hz
    refine ⟨?_, bot_lt_iff_ne_bot.mpr (support_ne_bot (fiber_nonempty hz) c),
      width_nonneg (fiber_nonempty hz) c⟩
    simpa only [← EReal.neg_bot, EReal.neg_lt_neg_iff] using
      bot_lt_iff_ne_bot.mpr (support_ne_bot (fiber_nonempty hz) (-c))
  · intro hint c
    exact bounded_on_IZ (indexSet M) (index_convex hM.2.1)
      (fun z => supportFn (zProj M z) c + supportFn (zProj M z) (-c))
      (fun z hz => width_nonneg (fiber_nonempty hz) c)
      (fun _ hz₁ _ hz₂ _ ht ht1 => width_concave hM.2.1 c hz₁ hz₂ ht ht1) hint
