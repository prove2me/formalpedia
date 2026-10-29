-- Prove2me | solution 2 for IntMul.Kappa.R8.Bit.Oppbank.net0O2_LabGates_stage1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:21:02.433153+00:00
-- url     : https://prove2.me/submissions/e792a2dc-1271-4196-9921-78f434193875

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankEOKOPack2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankOneRun2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNet
import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Aux_EOKOvacA

open IntMul.Kappa.R6.Bit Matrix
open scoped Kronecker

theorem labGates_sub {R : Type*} [CommRing R] {m : ℕ} {Wr : Type*} [Fintype Wr] [DecidableEq Wr]
    (N : ℕ) [Subsingleton (ZMod N)] :
    ∀ (l : List (Instr Wr R m)) (F : Wr → Matrix (Fin (m + m)) (Fin (m + m)) (ZMod N)),
      LabGates N l F
  | [], _ => by simp only [LabGates]
  | i :: l, F => by
      simp only [LabGates]
      refine ⟨?_, labGates_sub N l _⟩
      cases i with
      | gate g S => intro w _ w' _; exact Subsingleton.elim _ _
      | edge w e => trivial

abbrev TRm (X : Matrix (Fin (529 + 529)) (Fin (529 + 529)) ℚ) : Matrix (Fin 529) (Fin 529) ℚ :=
  X.submatrix (Fin.castAdd 529) (Fin.natAdd 529)

theorem ca_lt_na (i j : Fin 529) : Fin.castAdd 529 i < Fin.natAdd 529 j := by
  rw [Fin.lt_def]; simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega

theorem tr_mul_left (X Y : Matrix (Fin (529 + 529)) (Fin (529 + 529)) ℚ)
    (hX : ∀ i j, i < j → X i j = 0) :
    TRm (X * Y) = X.submatrix (Fin.castAdd 529) (Fin.castAdd 529) * TRm Y := by
  ext i j
  simp only [TRm, submatrix_apply, mul_apply]
  rw [Fin.sum_univ_add]
  have : ∑ k : Fin 529, X (Fin.castAdd 529 i) (Fin.natAdd 529 k) *
      Y (Fin.natAdd 529 k) (Fin.natAdd 529 j) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hX _ _ (ca_lt_na i k), zero_mul]
  rw [this, add_zero]

theorem tr_mul_right (Y X : Matrix (Fin (529 + 529)) (Fin (529 + 529)) ℚ)
    (hX : ∀ i j, i < j → X i j = 0) :
    TRm (Y * X) = TRm Y * X.submatrix (Fin.natAdd 529) (Fin.natAdd 529) := by
  ext i j
  simp only [TRm, submatrix_apply, mul_apply]
  rw [Fin.sum_univ_add]
  have : ∑ k : Fin 529, Y (Fin.castAdd 529 i) (Fin.castAdd 529 k) *
      X (Fin.castAdd 529 k) (Fin.natAdd 529 j) = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [hX _ _ (ca_lt_na k j), mul_zero]
  rw [this, zero_add]

theorem prod_swaps_fix {n : ℕ} : ∀ (L : List (Fin n × Fin n)) (x : Fin n),
    (∀ p ∈ L, p.1 ≠ x ∧ p.2 ≠ x) → (L.map fun p => Equiv.swap p.1 p.2).prod x = x
  | [], x, _ => by simp
  | p :: L, x, h => by
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
        prod_swaps_fix L x (fun q hq => h q (List.mem_cons_of_mem _ hq))]
      exact Equiv.swap_apply_of_ne_of_ne (h p List.mem_cons_self).1.symm
        (h p List.mem_cons_self).2.symm

theorem runPiv22_mem (p : Fin (529 + 529) × Fin (529 + 529))
    (hp : p ∈ runPiv 529 (0, 0, 22)) :
    ∃ k : Fin 529, k.val < 22 ∧ p.1 = Fin.castAdd 529 k ∧
      ∃ k' : Fin 529, p.2 = Fin.natAdd 529 k' := by
  unfold runPiv at hp
  rw [List.mem_filterMap] at hp
  obtain ⟨a, ha, hfa⟩ := hp
  rw [List.mem_range] at ha
  split_ifs at hfa with hh
  cases hfa
  exact ⟨⟨0 + a, hh.1⟩, show 0 + a < 22 by have ha' : a < 22 := ha; omega, rfl, ⟨0 + a, hh.2⟩, rfl⟩

theorem rank_le_22 (e : Edge 529) (q : Matrix (Fin 529) (Fin 529) ℚ) (hq : NB.EdgeQ e q)
    (hruns : e.runs = [(0, 0, 22)]) : q.rank ≤ 22 := by
  obtain ⟨-, hL1, -, hL2, -, heq⟩ := hq
  have hq' : q = TRm (NB.pswQ q) := by
    ext i j
    simp only [TRm, NB.pswQ, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂]
  rw [hq', ← heq, tr_mul_right _ _ hL2, tr_mul_left _ _ hL1]
  refine (rank_mul_le_left _ _).trans ((rank_mul_le_right _ _).trans ?_)
  generalize hσ : (List.map (fun p : Fin (529 + 529) × Fin (529 + 529) => Equiv.swap p.1 p.2)
    (List.flatMap (runPiv 529) e.runs)).prod = σ
  have hcard : (Finset.univ.image (fun k : Fin 22 => (Fin.castLE (by norm_num) k : Fin 529))).card
      ≤ 22 := Finset.card_image_le.trans (by simp)
  refine (rank_le_card_of_support_subset _
    (Finset.univ.image (fun k : Fin 22 => (Fin.castLE (by norm_num) k : Fin 529))) ?_).trans hcard
  intro i hi
  by_contra hge
  apply hi
  have hlt : ¬ i.val < 22 := fun h => hge (Finset.mem_coe.mpr (Finset.mem_image.mpr
    ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩))
  have hfix : σ (Fin.castAdd 529 i) = Fin.castAdd 529 i := by
    rw [← hσ]
    apply prod_swaps_fix
    intro p hp
    rw [List.mem_flatMap] at hp
    obtain ⟨r, hr, hp⟩ := hp
    rw [hruns, List.mem_singleton] at hr
    subst hr
    obtain ⟨k, hk, h1, k', h2⟩ := runPiv22_mem p hp
    rw [h1, h2]
    refine ⟨fun h => ?_, ne_of_gt (ca_lt_na i k')⟩
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd] at this
    omega
  funext j
  simp only [Matrix.row, TRm, submatrix_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, hfix,
    Pi.zero_apply, Option.mem_def, Option.some_inj]
  rw [if_neg (ne_of_lt (ca_lt_na i j))]

theorem rank_ge_23 (A : Matrix (Fin 23) (Fin 23) ℚ) (hA : A ≠ 0) :
    23 ≤ ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A).rank := by
  obtain ⟨i0, j0, h⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hA (Matrix.ext hc)
  have hsub : ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A).submatrix (fun k : Fin 23 => (k, i0))
      (fun k => (k, j0)) = diagonal (fun _ => A i0 j0) := by
    ext k k'
    simp only [submatrix_apply, kroneckerMap_apply, one_apply, diagonal_apply]
    split_ifs <;> simp
  have := rank_submatrix_le ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A) (fun k : Fin 23 => (k, i0))
    (fun k => (k, j0))
  rw [hsub, rank_diagonal] at this
  simpa [h] using this

theorem vmv_ne_one {R : Type*} [CommRing R] [Nontrivial R] (x y : Fin 23 → R) :
    vecMulVec x y ≠ 1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  rw [vecMulVec_apply, one_apply_eq] at h00 h11
  rw [vecMulVec_apply, one_apply_ne (by decide)] at h01 h10
  have : (x 0 * y 0) * (x 1 * y 1) = (x 0 * y 1) * (x 1 * y 0) := by ring
  rw [h00, h11, h01, h10] at this
  simp at this

theorem toGood_coe (N : ℕ) (x : AModelFac.goodSub N) : AModelFac.toGood N (x : ℚ) = x := by
  unfold AModelFac.toGood
  rw [dif_pos (show (x : ℚ).den.Coprime N from x.2)]

theorem coe_toGood (N : ℕ) (r : ℚ) (h : Nat.Coprime r.den N) :
    ((AModelFac.toGood N r : AModelFac.goodSub N) : ℚ) = r := by
  unfold AModelFac.toGood
  rw [dif_pos h]

theorem redQ_zero (N : ℕ) : AModelFac.redQ N 0 = 0 := by
  have : AModelFac.redQ N ((0 : AModelFac.goodSub N) : ℚ) = AModelFac.redHom N 0 := by
    unfold AModelFac.redQ; rw [toGood_coe]
  simpa using this

theorem redQ_one (N : ℕ) : AModelFac.redQ N 1 = 1 := by
  have : AModelFac.redQ N ((1 : AModelFac.goodSub N) : ℚ) = AModelFac.redHom N 1 := by
    unfold AModelFac.redQ; rw [toGood_coe]
  simpa using this

def lift (N : ℕ) {a b : Type*} (M : Matrix a b ℚ) : Matrix a b (AModelFac.goodSub N) :=
  fun i j => AModelFac.toGood N (M i j)

theorem lift_map (N : ℕ) {a b : Type*} (M : Matrix a b ℚ) (hM : ∀ i j, Nat.Coprime (M i j).den N) :
    (lift N M).map (AModelFac.goodSub N).subtype = M := by
  ext i j
  exact coe_toGood N _ (hM i j)

theorem kron_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin 23) (Fin 23) R) : (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by
  ext i j
  simp [kroneckerMap_apply, map_mul]

theorem edgeMat_dflt (N : ℕ) : edgeMat N (⟨1, [], 1⟩ : Edge 529) = 1 := by
  have h1 : redM N (1 : QMat2 529) = 1 := Matrix.map_one _ (redQ_zero N) (redQ_one N)
  simp only [edgeMat, h1, List.flatMap_nil, List.map_nil, List.prod_nil, Matrix.one_mul,
    Matrix.mul_one]
  exact permMatrix_one


theorem no_witness_gen (S0 : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ)
    (Si0 : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ) (hSi : Si0 * S0 = 1) (x y : Fin 23 → ℚ)
    (e : Edge 529) (he : NB.EdgeQ e (S0 * ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ
      (1 - vecMulVec x y)) * Si0)) (hruns : e.runs = [(0, 0, 22)]) : False := by
  have h1 := rank_le_22 e _ he hruns
  have hA0 : (1 : Matrix (Fin 23) (Fin 23) ℚ) - vecMulVec x y ≠ 0 := fun h0 =>
    vmv_ne_one x y (sub_eq_zero.mp h0).symm
  have h2 := rank_ge_23 _ hA0
  have hKron : Si0 * (S0 * ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ (1 - vecMulVec x y)) * Si0) * S0 =
      (1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ (1 - vecMulVec x y) := by
    simp only [Matrix.mul_assoc]
    rw [hSi, Matrix.mul_one, ← Matrix.mul_assoc, hSi, Matrix.one_mul]
  rw [← hKron] at h2
  have h3 := (rank_mul_le_left (Si0 * (S0 * ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ
      (1 - vecMulVec x y)) * Si0)) S0).trans (rank_mul_le_right Si0 _)
  omega

theorem one_eq_zero_gen (N : ℕ) (S0 : Matrix (Fin 529) (Fin 23 × Fin 23) ℚ)
    (Si0 : Matrix (Fin 23 × Fin 23) (Fin 529) ℚ) (hSi : Si0 * S0 = 1) (x y : Fin 23 → ℚ)
    (gS : ∀ i j, Nat.Coprime (S0 i j).den N) (gSi : ∀ i j, Nat.Coprime (Si0 i j).den N)
    (gP : ∀ i j, Nat.Coprime (vecMulVec x y i j).den N)
    (hmx : edgeMat N (⟨1, [], 1⟩ : Edge 529) = redM N (NB.pswQ (S0 * ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ
      (1 - vecMulVec x y)) * Si0))) : (1 : ZMod N) = 0 := by
  rw [edgeMat_dflt] at hmx
  obtain ⟨A, hAdef⟩ : ∃ A, A = (1 : Matrix (Fin 23) (Fin 23) ℚ) - vecMulVec x y := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = S0 * ((1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A) * Si0 := ⟨_, rfl⟩
  rw [← hAdef, ← hqdef] at hmx
  have hKron : Si0 * q * S0 = (1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A := by
    rw [hqdef]
    simp only [Matrix.mul_assoc]
    rw [hSi, Matrix.mul_one, ← Matrix.mul_assoc, hSi, Matrix.one_mul]
  have hq0 : ∀ i j, AModelFac.redQ N (q i j) = 0 := by
    intro i j
    have := congrFun (congrFun hmx (Fin.castAdd 529 i)) (Fin.natAdd 529 j)
    rw [Matrix.one_apply_ne (ne_of_lt (ca_lt_na i j))] at this
    simp only [redM, NB.pswQ, map_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂] at this
    exact this.symm
  set ι := (AModelFac.goodSub N).subtype with hι
  set φ := AModelFac.redHom N with hφ
  set P' := lift N (vecMulVec x y) with hP'
  set K' := lift N S0 *
    ((1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)) ⊗ₖ (1 - P')) * lift N Si0 with hK'
  have hA' : (1 - P').map ι = A := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hP',
      lift_map N _ gP, hAdef]
  have h1map : (1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)).map ι = 1 := by
    rw [← RingHom.mapMatrix_apply, map_one]
  have hkr : ((1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)) ⊗ₖ (1 - P')).map ι =
      (1 : Matrix (Fin 23) (Fin 23) ℚ) ⊗ₖ A := by
    rw [kron_map, h1map, hA']
  have hKmap : K'.map ι = q := by
    rw [hK', Matrix.map_mul, Matrix.map_mul, hkr, lift_map N _ gS, lift_map N _ gSi, hqdef]
  have hφK : K'.map φ = 0 := by
    ext i j
    rw [map_apply, Matrix.zero_apply, ← toGood_coe N (K' i j)]
    have : ((K' i j : AModelFac.goodSub N) : ℚ) = q i j := by
      rw [← hKmap]; rfl
    rw [this]
    exact hq0 i j
  have hconj : lift N Si0 * K' * lift N S0 =
      (1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)) ⊗ₖ (1 - P') := by
    apply Matrix.map_injective (f := ι) Subtype.val_injective
    show (lift N Si0 * K' * lift N S0).map ι =
      ((1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)) ⊗ₖ (1 - P')).map ι
    rw [Matrix.map_mul, Matrix.map_mul, hKmap, hkr, lift_map N _ gS, lift_map N _ gSi, hKron]
  have hz : ((1 : Matrix (Fin 23) (Fin 23) (AModelFac.goodSub N)) ⊗ₖ (1 - P')).map φ = 0 := by
    rw [← hconj, Matrix.map_mul, Matrix.map_mul, hφK, Matrix.mul_zero, Matrix.zero_mul]
  have hent : ∀ i j, φ ((1 - P') i j) = 0 := by
    intro i j
    have := congrFun (congrFun hz (0, i)) (0, j)
    rw [map_apply, kroneckerMap_apply, one_apply_eq, one_mul, Matrix.zero_apply] at this
    exact this
  have hd : ∀ i, φ (P' i i) = 1 := by
    intro i
    have := hent i i
    rw [Matrix.sub_apply, one_apply_eq, map_sub, map_one, sub_eq_zero] at this
    exact this.symm
  have ho : ∀ i j, i ≠ j → φ (P' i j) = 0 := by
    intro i j hij
    have := hent i j
    rw [Matrix.sub_apply, one_apply_ne hij, map_sub, map_zero, zero_sub, neg_eq_zero] at this
    exact this
  have hid : P' 0 0 * P' 1 1 = P' 0 1 * P' 1 0 := by
    apply Subtype.val_injective
    simp only [Subring.coe_mul]
    have e : ∀ i j, ((P' i j : AModelFac.goodSub N) : ℚ) = vecMulVec x y i j :=
      fun i j => coe_toGood N _ (gP i j)
    rw [e, e, e, e]
    simp only [vecMulVec_apply]
    ring
  have := congrArg φ hid
  rw [map_mul, map_mul, hd, hd, ho 0 1 (by decide), ho 1 0 (by decide)] at this
  simpa using this


theorem pickE_none (P : Edge 529 → Prop) (h : ¬ ∃ e, P e) :
    IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.pickE P = ⟨1, [], 1⟩ := by
  (unfold IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.pickE; rw [dif_neg h]) <;> rfl

theorem one_eq_zero (N : ℕ) (h : IntMul.Kappa.R8.Bit.Oppbank.EOKO2.EOKO
    IntMul.Kappa.R8.Bit.Oppbank.EOKO2.ch0NB N) : (1 : ZMod N) = 0 := by
  have hSi : IntMul.Kappa.R8.Bit.Oppbank.Pnd.Si0 * IntMul.Kappa.R8.Bit.Oppbank.Pnd.S0 = 1 := h.hSi
  have hno : ¬ ∃ e, IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.PE
      (IntMul.Kappa.R8.Bit.Oppbank.Pnd.K IntMul.Kappa.R8.Bit.Oppbank.Pnd.S0
        IntMul.Kappa.R8.Bit.Oppbank.Pnd.Si0 1 (1 - IntMul.Kappa.R8.Bit.Oppbank.Pnd.Pl 0))
      (IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.oneRun 22) e := by
    rintro ⟨e, he, hr⟩
    exact no_witness_gen IntMul.Kappa.R8.Bit.Oppbank.Pnd.S0 IntMul.Kappa.R8.Bit.Oppbank.Pnd.Si0
      hSi (IntMul.Kappa.R8.Bit.Oppbank.Pnd.xv 0) (IntMul.Kappa.R8.Bit.Oppbank.Pnd.yv 0) e he hr.2.2
  have h2 : IntMul.Kappa.R8.Bit.Oppbank.EOKO2.ch0NB.ex 0 =
      (if 0 < 1771 then IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.pickE
        (IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.PE
          (IntMul.Kappa.R8.Bit.Oppbank.Pnd.K IntMul.Kappa.R8.Bit.Oppbank.Pnd.S0
            IntMul.Kappa.R8.Bit.Oppbank.Pnd.Si0 1 (1 - IntMul.Kappa.R8.Bit.Oppbank.Pnd.Pl 0))
          (IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2.oneRun 22))
      else (⟨1, [], 1⟩ : Edge 529)) := rfl
  have hex : IntMul.Kappa.R8.Bit.Oppbank.EOKO2.ch0NB.ex 0 = (⟨1, [], 1⟩ : Edge 529) := by
    rw [h2, if_pos (by norm_num)]
    exact pickE_none _ hno
  have hmx := h.mx 0 (by norm_num)
  rw [hex] at hmx
  exact one_eq_zero_gen N IntMul.Kappa.R8.Bit.Oppbank.Pnd.S0 IntMul.Kappa.R8.Bit.Oppbank.Pnd.Si0
    hSi (IntMul.Kappa.R8.Bit.Oppbank.Pnd.xv 0) (IntMul.Kappa.R8.Bit.Oppbank.Pnd.yv 0)
    h.gS h.gSi (h.gPl 0 (by norm_num)) hmx

end Aux_EOKOvacA

open IntMul.Kappa.R8.Bit.Oppbank in
open IntMul.Kappa.R6.Bit (LabGates) in
open IntMul.Kappa.R8.Bit.Oppbank.EOKO2 in
open IntMul.Kappa.R8.Bit.Oppbank.OneRunNet2 in
open IntMul.Kappa.R8.Bit.Oppbank.NB (blk1) in
theorem solution (N : ℕ) (h : EOKO ch0NB N) :
    LabGates N ((List.range 1771).flatMap (blk1 (toNB ch0O))) (fun _ => 1) := by
  haveI : Subsingleton (ZMod N) := subsingleton_of_zero_eq_one (Aux_EOKOvacA.one_eq_zero N h).symm
  exact Aux_EOKOvacA.labGates_sub N _ _
