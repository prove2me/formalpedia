-- Prove2me | solution 1 for InfoLossLAR.WorstCase.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T23:21:55.674121+00:00
-- url     : https://prove2.me/submissions/7c4d8714-dd97-4907-a46f-514f40782bd3

import Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_4
import Mathlib
set_option autoImplicit false
open Matrix InfoLossLAR.WorstCase

namespace EndpointPullback
variable {d q : ℕ} [Fact q.Prime]
private theorem split_lift (z : Fin d → ℤ) :
    lift (modq q z) = z - (q : ℤ) • carry q z := by
  funext i
  change (((z i : ZMod q).val : ℤ)) = z i - (q : ℤ) * ⌊(z i : ℚ) / (q : ℚ)⌋
  rw [ZMod.val_intCast, Int.floor_div_natCast, Int.floor_intCast]
  have h := Int.emod_add_mul_ediv (z i) q
  omega

private theorem reduce_sub (z a : Fin d → ℤ) :
    modq q (z - (q : ℤ) • a) = modq q z := by
  funext i
  change ((z i - (q : ℤ) * a i : ℤ) : ZMod q) = _
  simp [modq]

private theorem cT_preimage
    (hT : IsRoundingMatrix q (d-1) d (TDef63 q d))
    (w : Fin d → ZMod q) (z : Fin d → ℤ) (hz : (TDef63 q d) *ᵥ z = lift w) :
    cT q d w = modq q z := by
  obtain ⟨S⟩ := hT
  have hdiag : (smithDiag q (d-1) d).det ≠ 0 := by
    rw [smithDiag, Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    split_ifs <;> simp [NeZero.ne q]
  have hn : (TDef63 q d).det ≠ 0 := by
    intro hz'
    apply hdiag
    rw [← S.smith, Matrix.det_mul, Matrix.det_mul,hz',mul_zero,zero_mul]
  let A := (TDef63 q d).map (Int.cast : ℤ → ℚ)
  have ha : IsUnit A.det := by
    rw [isUnit_iff_ne_zero]
    have hmap := (Int.castRingHom ℚ).map_det (TDef63 q d)
    change ((TDef63 q d).det : ℚ) = A.det at hmap
    rw [← hmap]
    exact_mod_cast hn
  have hc : (fun j => (lift w j : ℚ)) = A *ᵥ (fun j => (z j : ℚ)) := by
    funext i
    rw [← hz]
    simp [A, Matrix.mulVec, dotProduct]
  unfold cT TinvQ
  change (fun i => (((A⁻¹ *ᵥ (fun j => (lift w j : ℚ))) i).num : ZMod q)) = _
  rw [hc,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A ha,Matrix.one_mulVec]
  funext i
  exact congrArg (fun a : ℤ => (a : ZMod q)) (Rat.num_intCast _)


omit [Fact q.Prime] in
private theorem endpoint_maps (T : Matrix (Fin d) (Fin d) ℤ)
    (L : ∀ z, z ∈ imageLattice T ↔ (q : ℤ) ∣ ∑ j, z j) (x : Fin d → ℤ) :
    modq q (T *ᵥ x) ∈ H0 q d := by
  have h := (L _).mp ⟨x, rfl⟩
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
  simpa [modq, H0] using h'

private theorem lift_mod (x : Fin d → ZMod q) : modq q (lift x) = x := by
  funext i
  simp [modq,lift]

private theorem from_hyperplane (hq2 : q ≠ 2) (hdq : q ≤ d)
    (w : Fin d → ZMod q) (hw : w ∈ H0 q d) :
    cT q d w ∈ zeroFiber63 q d ∧ modq q ((TDef63 q d) *ᵥ lift (cT q d w)) = w := by
  obtain ⟨L,_,hT⟩ := lemma_6_4 q d Fact.out hq2 hdq
  have hwz : (q : ℤ) ∣ ∑ i, lift w i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    simpa [lift, H0] using hw
  obtain ⟨z, hz⟩ := (L _).mpr hwz
  change TDef63 q d *ᵥ z = lift w at hz
  rw [cT_preimage hT w z hz]
  let a := TDef63 q d *ᵥ carry q z
  have hrep : TDef63 q d *ᵥ lift (modq q z) = lift w - (q : ℤ) • a := by
    rw [split_lift, mulVec_sub,mulVec_smul,hz]
  constructor
  · change ((∑ i, carry q (TDef63 q d *ᵥ lift (modq q z)) i : ℤ) : ZMod q) = 0
    have hc (i : Fin d) : carry q (TDef63 q d *ᵥ lift (modq q z)) i = - a i := by
      rw [hrep]
      change ⌊(((lift w i - (q : ℤ) * a i : ℤ) : ℚ) / (q : ℚ))⌋ = -a i
      rw [Int.floor_div_natCast, Int.floor_intCast,Int.sub_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne q)]
      have hm : lift w i / (q : ℤ) = 0 := by
        apply Int.ediv_eq_zero_of_lt
        · exact Int.natCast_nonneg _
        · change ((w i).val : ℤ) < (q : ℤ)
          exact_mod_cast ZMod.val_lt (w i)
      rw [hm,zero_sub]
    simp_rw [hc]
    rw [Finset.sum_neg_distrib, Int.cast_neg, neg_eq_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr ((L _).mp ⟨carry q z,rfl⟩)
  · rw [hrep, reduce_sub, lift_mod]

private theorem from_fiber (hq2 : q ≠ 2) (hdq : q ≤ d) (x : Fin d → ZMod q)
    (hx : x ∈ zeroFiber63 q d) :
    modq q ((TDef63 q d) *ᵥ lift x) ∈ H0 q d ∧
    cT q d (modq q ((TDef63 q d) *ᵥ lift x)) = x := by
  obtain ⟨L,_,hT⟩ := lemma_6_4 q d Fact.out hq2 hdq
  exact ⟨endpoint_maps _ L _, by
    let y := (TDef63 q d) *ᵥ lift x
    have hcarry : (q : ℤ) ∣ ∑ i, carry q y i :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hx
    obtain ⟨u,hu⟩ := (L _).mpr hcarry
    change TDef63 q d *ᵥ u = carry q y at hu
    have hp : TDef63 q d *ᵥ (lift x - (q : ℤ) • u) = lift (modq q y) := by
      rw [split_lift,mulVec_sub,mulVec_smul,hu]
    exact (cT_preimage hT _ _ hp).trans ((reduce_sub (lift x) u).trans (lift_mod x))⟩

theorem _root_.solution (q d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hdq : q ≤ d) :
    Set.BijOn (cT q d) (H0 q d) (zeroFiber63 q d) ∧
    ∀ x ∈ zeroFiber63 q d,
      modq q ((TDef63 q d).mulVec (lift x)) ∈ H0 q d ∧
      cT q d (modq q ((TDef63 q d).mulVec (lift x))) = x := by
  refine ⟨⟨fun w hw => (from_hyperplane hq2 hdq w hw).1, ?_, ?_⟩, from_fiber hq2 hdq⟩
  · intro a ha b hb he
    have h := congrArg (fun x => modq q (TDef63 q d *ᵥ lift x)) he
    exact (from_hyperplane hq2 hdq a ha).2.symm.trans (h.trans (from_hyperplane hq2 hdq b hb).2)
  · intro x hx
    obtain ⟨hw,hx'⟩ := from_fiber hq2 hdq x hx
    exact ⟨_,hw,hx'⟩
end EndpointPullback
