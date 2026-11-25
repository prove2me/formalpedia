-- Prove2me | solution 1 for Matrix.SpecialLinearGroup.sum_conjClasses_det_trace_eq_hurwitzClassNumber
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:31:59.727933+00:00
-- url     : https://prove2.me/submissions/2d3e336f-ae4c-4498-91cd-2a9773954f47

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesD

set_option autoImplicit false

open scoped MatrixGroups

namespace UploadConjSW33

open RamanujanPetersson.S3 RamanujanPetersson.S3.Conj RamanujanPetersson.Hurwitz CongruenceSubgroup

/-! ## Class sums written with `Quot` (the posted statement's form) -/

/-- Conjugacy by `SL₂(ℤ)` on matrices satisfying `P`. -/
def CRel (P : Mat → Prop) (x y : {γ : Mat // P γ}) : Prop :=
  ∃ g : SL(2, ℤ), (g : Mat) * x.1 = y.1 * g

/-- `1 / #centraliser`. -/
noncomputable def wt (γ : Mat) : ℚ :=
  1 / Nat.card {g : SL(2, ℤ) // (g : Mat) * γ = γ * g}

/-- The class sum over the `SL₂(ℤ)`-classes of `{γ | P γ}`. -/
noncomputable def qSum (P : Mat → Prop) : ℚ :=
  ∑ᶠ C : Quot (CRel P), wt C.out.1

theorem mem_G1 (g : SL(2, ℤ)) : g ∈ Gamma1 1 := (mem_Gamma1_iff 1 g).2 (Subsingleton.elim _ _)

theorem rel_iff_conj (g : SL(2, ℤ)) (a b : Mat) : (g : Mat) * a = b * g ↔ conj g a = b := by
  constructor
  · intro hg
    simp only [conj]
    rw [hg, Matrix.mul_assoc, coe_mul_coe_inv, Matrix.mul_one]
  · intro hb
    rw [← hb]
    simp only [conj, Matrix.mul_assoc, coe_inv_mul_coe, Matrix.mul_one]

theorem conj_mul_conj (g : SL(2, ℤ)) (X Y : Mat) : conj g X * conj g Y = conj g (X * Y) := by
  simp only [conj, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((g⁻¹ : SL(2, ℤ)) : Mat) (g : Mat), coe_inv_mul_coe, Matrix.one_mul]

theorem coe_mulAut_conj (g k : SL(2, ℤ)) : ((MulAut.conj g k : SL(2, ℤ)) : Mat) = conj g k := by
  simp [conj, MulAut.conj_apply, Matrix.SpecialLinearGroup.coe_mul]

/-- The centraliser weight is a class function. -/
theorem wt_of_rel {a b : Mat} (g : SL(2, ℤ)) (hg : (g : Mat) * a = b * g) : wt a = wt b := by
  have hb : conj g a = b := (rel_iff_conj g a b).1 hg
  have e : {k : SL(2, ℤ) // (k : Mat) * a = a * k} ≃ {k : SL(2, ℤ) // (k : Mat) * b = b * k} :=
    Equiv.subtypeEquiv (MulAut.conj g).toEquiv fun k => by
      show (k : Mat) * a = a * k ↔ ((MulAut.conj g k : SL(2, ℤ)) : Mat) * b = b * (MulAut.conj g k : SL(2, ℤ))
      rw [coe_mulAut_conj, ← hb, conj_mul_conj, conj_mul_conj]
      constructor
      · intro h; rw [h]
      · intro h
        have h' := congrArg (conj g⁻¹) h
        rwa [conj_inv_conj, conj_inv_conj] at h'
  unfold wt
  rw [Nat.card_congr e]

theorem wt_of_eqvGen (P : Mat → Prop) (a b : {γ : Mat // P γ}) (h : Relation.EqvGen (CRel P) a b) :
    wt a.1 = wt b.1 := by
  induction h with
  | rel x y hxy => obtain ⟨g, hg⟩ := hxy; exact wt_of_rel g hg
  | refl => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem wt_out (P : Mat → Prop) (x : {γ : Mat // P γ}) : wt (Quot.mk (CRel P) x).out.1 = wt x.1 :=
  wt_of_eqvGen P _ _ (Quot.eqvGen_exact (Quot.out_eq (Quot.mk (CRel P) x)))

/-! ## Bridge to the library's `classSum` over `Γ₁(1) = SL₂(ℤ)` -/

section Bridge

variable (P : Mat → Prop) (S : Set Mat) [MulAction (Gamma1 1) S]
  (hs : ∀ (h : Gamma1 1) (x : S), ((h • x : S) : Mat) = conj (h : SL(2, ℤ)) x)
  (hP : ∀ γ, P γ ↔ γ ∈ S)

include hs in
theorem crel_iff (a b : {γ : Mat // P γ}) (ea eb : S) (ha : (ea : Mat) = a.1) (hb : (eb : Mat) = b.1) :
    CRel P a b ↔ (MulAction.orbitRel (Gamma1 1) S) ea eb := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨⟨g⁻¹, mem_G1 _⟩, Subtype.ext ?_⟩
    rw [hs, ha, hb]
    show conj g⁻¹ b.1 = a.1
    rw [← (rel_iff_conj g a.1 b.1).1 hg, conj_inv_conj]
  · rintro ⟨h, hh⟩
    have h1 : conj (h : SL(2, ℤ)) b.1 = a.1 := by
      have := congrArg Subtype.val hh
      rw [hs, hb, ha] at this
      exact this
    refine ⟨(h : SL(2, ℤ))⁻¹, (rel_iff_conj _ _ _).2 ?_⟩
    rw [← h1, conj_inv_conj]

/-- `Quot (CRel P) ≃ Γ₁(1)\S`. -/
noncomputable def quotEquiv : Quot (CRel P) ≃ MulAction.orbitRel.Quotient (Gamma1 1) S :=
  Quot.congr (Equiv.subtypeEquivRight hP) fun a b =>
    crel_iff P S hs a b (Equiv.subtypeEquivRight hP a) (Equiv.subtypeEquivRight hP b) rfl rfl

/-- Stabiliser in `Γ₁(1)` = centraliser in `SL₂(ℤ)`. -/
def stabEquiv (x : S) :
    MulAction.stabilizer (Gamma1 1) x ≃ {g : SL(2, ℤ) // (g : Mat) * x.1 = x.1 * g} where
  toFun h := ⟨h.1.1, (rel_iff_conj _ _ _).2 (by
    have := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 h.2)
    rw [hs] at this
    exact this)⟩
  invFun g := ⟨⟨g.1, mem_G1 _⟩, MulAction.mem_stabilizer_iff.2 (Subtype.ext (by
    rw [hs]
    exact (rel_iff_conj _ _ _).1 g.2))⟩
  left_inv h := rfl
  right_inv g := rfl

include hs hP in
theorem qSum_eq_classSum : qSum P = classSum (Gamma1 1) S := by
  unfold qSum classSum
  rw [← finsum_comp_equiv (quotEquiv P S hs hP)]
  refine finsum_congr fun C => ?_
  have hE : quotEquiv P S hs hP C = Quotient.mk _ (Equiv.subtypeEquivRight hP C.out) := by
    conv_lhs => rw [← Quot.out_eq C]
    rfl
  rw [hE, card_stab_out]
  unfold wt
  exact congrArg (fun k : ℕ => (1 : ℚ) / k)
    (Nat.card_congr (stabEquiv S hs (Equiv.subtypeEquivRight hP C.out))).symm

end Bridge

/-! ## The three predicates and the split by the sign of `c` -/

abbrev Pall (n : ℕ) (t : ℤ) : Mat → Prop := fun γ => γ.det = n ∧ γ.trace = t
abbrev Ppos (n : ℕ) (t : ℤ) : Mat → Prop := fun γ => γ.det = n ∧ γ.trace = t ∧ 0 < γ 1 0
abbrev Pneg (n : ℕ) (t : ℤ) : Mat → Prop := fun γ => γ.det = n ∧ γ.trace = t ∧ γ 1 0 < 0

section Split

variable {n : ℕ} {t : ℤ}

theorem lower_ne_zero (ht : t ^ 2 < 4 * (n : ℤ)) {γ : Mat} (hd : γ.det = n) (htr : γ.trace = t) :
    γ 1 0 ≠ 0 := by
  intro hc
  rw [Matrix.det_fin_two, hc] at hd
  rw [Matrix.trace_fin_two] at htr
  rw [← htr, ← hd] at ht
  nlinarith [sq_nonneg (γ 0 0 - γ 1 1)]

theorem mem_EllPos_one (ht : t ^ 2 < 4 * (n : ℤ)) (γ : Mat) :
    Ppos n t γ ↔ γ ∈ EllPos 1 (1 : ZMod 1) t n := by
  rw [mem_EllPos_iff']
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c, ht, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
    fun ⟨a, b, c, _⟩ => ⟨a, b, c⟩⟩

theorem mem_EllNeg_one (ht : t ^ 2 < 4 * (n : ℤ)) (γ : Mat) :
    Pneg n t γ ↔ γ ∈ EllNeg 1 (1 : ZMod 1) t n := by
  rw [mem_EllNeg_iff']
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, c, ht, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
    fun ⟨a, b, c, _⟩ => ⟨a, b, c⟩⟩

theorem pos_of_rel (ht : t ^ 2 < 4 * (n : ℤ)) {x y : Mat} (hx : Pall n t x) (g : SL(2, ℤ))
    (hg : (g : Mat) * x = y * g) (hpos : 0 < x 1 0) : 0 < y 1 0 := by
  have hxS : x ∈ EllPos 1 (1 : ZMod 1) t n := (mem_EllPos_one ht x).1 ⟨hx.1, hx.2, hpos⟩
  have hyS : conj g x ∈ EllPos 1 (1 : ZMod 1) t n :=
    ((⟨g, mem_G1 g⟩ : Gamma1 1) • (⟨x, hxS⟩ : EllPos 1 (1 : ZMod 1) t n)).2
  rw [(rel_iff_conj g x y).1 hg] at hyS
  exact ((mem_EllPos_one ht y).2 hyS).2.2

theorem rel_symm {x y : Mat} (g : SL(2, ℤ)) (hg : (g : Mat) * x = y * g) :
    ((g⁻¹ : SL(2, ℤ)) : Mat) * y = x * ((g⁻¹ : SL(2, ℤ)) : Mat) := by
  rw [rel_iff_conj]
  rw [← (rel_iff_conj g x y).1 hg, conj_inv_conj]

theorem pos_iff_of_rel (ht : t ^ 2 < 4 * (n : ℤ)) {x y : {γ : Mat // Pall n t γ}}
    (hxy : CRel (Pall n t) x y) : 0 < x.1 1 0 ↔ 0 < y.1 1 0 := by
  obtain ⟨g, hg⟩ := hxy
  exact ⟨pos_of_rel ht x.2 g hg, pos_of_rel ht y.2 g⁻¹ (rel_symm g hg)⟩

theorem neg_of_not_pos (ht : t ^ 2 < 4 * (n : ℤ)) (x : {γ : Mat // Pall n t γ}) (h : ¬ 0 < x.1 1 0) :
    x.1 1 0 < 0 :=
  lt_of_le_of_ne (not_lt.1 h) (lower_ne_zero ht x.2.1 x.2.2)

noncomputable def splitFun (ht : t ^ 2 < 4 * (n : ℤ)) :
    Quot (CRel (Pall n t)) → Quot (CRel (Ppos n t)) ⊕ Quot (CRel (Pneg n t)) :=
  Quot.lift
    (fun x => if h : 0 < x.1 1 0 then Sum.inl (Quot.mk _ ⟨x.1, x.2.1, x.2.2, h⟩)
      else Sum.inr (Quot.mk _ ⟨x.1, x.2.1, x.2.2, neg_of_not_pos ht x h⟩))
    (fun x y hxy => by
      have hiff := pos_iff_of_rel ht hxy
      by_cases hx : 0 < x.1 1 0
      · rw [dif_pos hx, dif_pos (hiff.1 hx)]
        exact congrArg Sum.inl (Quot.sound hxy)
      · rw [dif_neg hx, dif_neg (fun h => hx (hiff.2 h))]
        exact congrArg Sum.inr (Quot.sound hxy))

noncomputable def splitInv : Quot (CRel (Ppos n t)) ⊕ Quot (CRel (Pneg n t)) → Quot (CRel (Pall n t)) :=
  Sum.elim (Quot.map (fun x => ⟨x.1, x.2.1, x.2.2.1⟩) (fun _ _ h => h))
    (Quot.map (fun x => ⟨x.1, x.2.1, x.2.2.1⟩) (fun _ _ h => h))

noncomputable def splitEquiv (ht : t ^ 2 < 4 * (n : ℤ)) :
    Quot (CRel (Pall n t)) ≃ Quot (CRel (Ppos n t)) ⊕ Quot (CRel (Pneg n t)) where
  toFun := splitFun ht
  invFun := splitInv
  left_inv C := by
    obtain ⟨x, rfl⟩ := Quot.exists_rep C
    by_cases h : 0 < x.1 1 0
    · have : splitFun ht (Quot.mk _ x) = Sum.inl (Quot.mk _ ⟨x.1, x.2.1, x.2.2, h⟩) := dif_pos h
      rw [this]
      rfl
    · have : splitFun ht (Quot.mk _ x) =
          Sum.inr (Quot.mk _ ⟨x.1, x.2.1, x.2.2, neg_of_not_pos ht x h⟩) := dif_neg h
      rw [this]
      rfl
  right_inv D := by
    rcases D with C | C
    · obtain ⟨x, rfl⟩ := Quot.exists_rep C
      show splitFun ht (Quot.mk _ ⟨x.1, x.2.1, x.2.2.1⟩) = _
      exact dif_pos x.2.2.2
    · obtain ⟨x, rfl⟩ := Quot.exists_rep C
      show splitFun ht (Quot.mk _ ⟨x.1, x.2.1, x.2.2.1⟩) = _
      exact dif_neg (not_lt.2 x.2.2.2.le)

theorem qSum_split (ht : t ^ 2 < 4 * (n : ℤ)) [Finite (Quot (CRel (Ppos n t)))]
    [Finite (Quot (CRel (Pneg n t)))] :
    qSum (Pall n t) = qSum (Ppos n t) + qSum (Pneg n t) := by
  have := Fintype.ofFinite (Quot (CRel (Ppos n t)))
  have := Fintype.ofFinite (Quot (CRel (Pneg n t)))
  unfold qSum
  rw [← finsum_comp_equiv (splitEquiv ht).symm, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun C _ => ?_
    obtain ⟨x, rfl⟩ := Quot.exists_rep C
    show wt (Quot.mk (CRel (Pall n t)) ⟨x.1, x.2.1, x.2.2.1⟩).out.1 = wt (Quot.mk _ x).out.1
    rw [wt_out, wt_out]
  · refine Finset.sum_congr rfl fun C _ => ?_
    obtain ⟨x, rfl⟩ := Quot.exists_rep C
    show wt (Quot.mk (CRel (Pall n t)) ⟨x.1, x.2.1, x.2.2.1⟩).out.1 = wt (Quot.mk _ x).out.1
    rw [wt_out, wt_out]

end Split

/-! ## The textbook `H(N)` is the library's `hurwitzH` -/

theorem mem_box_iff (n : ℕ) (t : ℤ) (hlt : t ^ 2 < 4 * (n : ℤ)) (a b c : ℤ) :
    ((a, b, c) ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
          Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
            r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
              (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1)))) ↔
      (a, b, c) ∈ redForms (t ^ 2 - 4 * n) := by
  rw [mem_redForms, Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc, Finset.mem_Icc]
  simp only [toBQF, BQF.disc, BQF.IsReduced]
  constructor
  · rintro ⟨⟨⟨ha1, _⟩, _, _⟩, hd, habs, hac, hbd⟩
    obtain ⟨hb1, hb2⟩ := abs_le.1 habs
    refine ⟨hd, ?_, hb2, hac, fun h => hbd (Or.inr h)⟩
    by_contra hcon
    have hbeq : b = -a := by omega
    have habs' : |b| = a := by rw [hbeq, abs_neg, abs_of_pos (by omega)]
    have := hbd (Or.inl habs')
    omega
  · rintro ⟨hd, h1, h2, h3, h4⟩
    have ha0 : 0 < a := by omega
    have hc0 : 0 < c := by omega
    have hb2 : b ^ 2 ≤ a ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (le_of_lt (by linarith : (0 : ℤ) < a + b))]
    have hac2 : a * a ≤ a * c := mul_le_mul_of_nonneg_left h3 ha0.le
    have h4ac : 4 * a * c ≤ a ^ 2 + 4 * n := by nlinarith [sq_nonneg t]
    have hacn : 3 * (a * c) ≤ 4 * n := by nlinarith
    have hA : a ≤ a * c := by nlinarith
    have hC : c ≤ a * c := by nlinarith
    refine ⟨⟨⟨by omega, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by omega, by linarith⟩⟩, hd,
      abs_le.2 ⟨by linarith, h2⟩, h3, ?_⟩
    rintro (h | h)
    · rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega
    · exact h4 h

theorem two_div_stabOrd (A B C : ℤ) : (2 : ℚ) / (stabOrd (A, B, C) : ℚ) =
    if A = B ∧ B = C then 1 / 3 else if B = 0 ∧ A = C then 1 / 2 else 1 := by
  unfold stabOrd
  dsimp only
  split_ifs <;> norm_num

theorem inline_eq (n : ℕ) (t : ℤ) (hlt : t ^ 2 < 4 * (n : ℤ)) :
    (∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
          Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
            r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
              (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
        (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
          else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) =
      hurwitzH (4 * (n : ℤ) - t ^ 2).toNat := by
  have hNz : (((4 * (n : ℤ) - t ^ 2).toNat : ℕ) : ℤ) = 4 * n - t ^ 2 := Int.toNat_of_nonneg (by linarith)
  have hN0 : (4 * (n : ℤ) - t ^ 2).toNat ≠ 0 := by
    intro h; rw [h] at hNz; push_cast at hNz; linarith
  rw [hurwitzH, if_neg hN0]
  have hD : (-(((4 * (n : ℤ) - t ^ 2).toNat : ℕ) : ℤ)) = t ^ 2 - 4 * n := by rw [hNz]; ring
  rw [hD]
  apply Finset.sum_congr
  · ext ⟨a, b, c⟩
    exact mem_box_iff n t hlt a b c
  · rintro ⟨a, b, c⟩ _
    exact (two_div_stabOrd a b c).symm

/-! ## Main -/

theorem main (n : ℕ) (t : ℤ) (ht : t ^ 2 < 4 * (n : ℤ)) (H : ℚ)
    (hH : H = ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
          Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
            r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
              (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
        (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
          else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) :
    qSum (Pall n t) = H ∧ qSum (Ppos n t) = H / 2 ∧ qSum (Pneg n t) = H / 2 := by
  have hHh : H = hurwitzH (4 * (n : ℤ) - t ^ 2).toNat := hH.trans (inline_eq n t ht)
  have h2 : 2 * ellCount 1 1 t n = hurwitzH (4 * (n : ℤ) - t ^ 2).toNat := level1Ell n t ht
  have hpos : qSum (Ppos n t) = ellCount 1 1 t n :=
    (qSum_eq_classSum _ (EllPos 1 (1 : ZMod 1) t n) (fun _ _ => rfl) (mem_EllPos_one ht)).trans
      (classSum_EllPos (1 : ZMod 1) t n)
  have hneg : qSum (Pneg n t) = ellCount 1 1 t n :=
    (qSum_eq_classSum _ (EllNeg 1 (1 : ZMod 1) t n) (fun _ _ => rfl) (mem_EllNeg_one ht)).trans
      (classSum_EllNeg 1 (1 : ZMod 1) t n)
  have : Finite (MulAction.orbitRel.Quotient (Gamma1 1) (EllPos 1 (1 : ZMod 1) t n)) :=
    finite_EllPos_quot (1 : ZMod 1) t n
  have : Finite (MulAction.orbitRel.Quotient (Gamma1 1) (EllNeg 1 (1 : ZMod 1) t n)) :=
    finite_EllNeg_quot 1 (1 : ZMod 1) t n
  have : Finite (Quot (CRel (Ppos n t))) :=
    Finite.of_equiv _ (quotEquiv _ (EllPos 1 (1 : ZMod 1) t n) (fun _ _ => rfl) (mem_EllPos_one ht)).symm
  have : Finite (Quot (CRel (Pneg n t))) :=
    Finite.of_equiv _ (quotEquiv _ (EllNeg 1 (1 : ZMod 1) t n) (fun _ _ => rfl) (mem_EllNeg_one ht)).symm
  have hall : qSum (Pall n t) = qSum (Ppos n t) + qSum (Pneg n t) := qSum_split ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hall, hpos, hneg, hHh, ← h2]; ring
  · rw [hpos, hHh, ← h2]; ring
  · rw [hneg, hHh, ← h2]; ring

end UploadConjSW33

theorem solution
    (n : ℕ) (t : ℤ) (ht : t ^ 2 < 4 * (n : ℤ)) (H : ℚ)
    (hH : H = ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
          Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
            r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
              (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
        (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
          else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) :
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) = H ∧
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t ∧ 0 < γ 1 0} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) =
        H / 2 ∧
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t ∧ γ 1 0 < 0} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) =
        H / 2 := by
  exact UploadConjSW33.main n t ht H hH

