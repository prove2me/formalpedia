-- Prove2me | solution 1 for LanglandsTunnell.liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b6850b6d-36d8-50ca-a2bd-8862da5931cd

import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_LanglandsTunnell_Lift48
import Theorems.Thm_LanglandsTunnell_exists_finset_forall_inertia_eq_bot
import Theorems.Thm_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow

set_option autoImplicit false

open NumberField IsDedekindDomain

open LanglandsTunnell LanglandsTunnell.P2 LanglandsTunnell.Lift48 FLT.ExplicitLift FrobeniusDensity

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (m : Mat) : m.map red = m.map redc := by
  ext i j; simp [Matrix.map_apply, red_eq_redc]

private theorem mem_map_redc_K48_of_det_ne_zero :
    ∀ m : Matrix (Fin 2) (Fin 2) (ZMod 3), m.det ≠ 0 → m ∈ K48.map (·.map redc) := by decide

private theorem lift_exists (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    ∃ M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat), M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨M, hM, hMg⟩ := List.mem_map.1 (mem_map_redc_K48_of_det_ne_zero _ hdet)
  exact ⟨M, (mem_closure_iff_mem_K48 M).2 hM, by rw [map_red_eq_map_redc]; exact hMg⟩

private theorem liftOf_spec (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf g ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧
      (liftOf g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Classical.epsilon_spec (p := fun M : Mat =>
    M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat) ∧ M.map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (lift_exists g)

private theorem det_liftOf (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (liftOf g).det = 1 ∨ (liftOf g).det = -1 := by
  have h := K48_det_cases _ ((mem_closure_iff_mem_K48 _).1 (liftOf_spec g).1)
  rwa [det2_eq_det] at h

private theorem eq_of_pm1_of_red_eq {x y : ℤ√(-2)} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (h : red x = red y) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · simp only [map_one, map_neg] at h
    exact absurd h (by decide)
  · simp only [map_neg, map_one] at h
    exact absurd h (by decide)
  · rfl

private theorem chiNegThree_cases (n : ℕ) :
    EisensteinWeightOne.chiNegThree n = 1 ∨ EisensteinWeightOne.chiNegThree n = -1 ∨
      EisensteinWeightOne.chiNegThree n = 0 := by
  unfold EisensteinWeightOne.chiNegThree
  split_ifs <;> simp

open Classical in
private theorem relDeg_spec {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) :
    0 < relDeg H σ ∧ σ ^ relDeg H σ ∈ H :=
  Nat.find_spec (exists_pos_pow_mem H σ)

open Classical in
private theorem relDeg_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G) {m : ℕ} (hm : 0 < m)
    (h : σ ^ m ∈ H) : relDeg H σ ≤ m :=
  Nat.find_min' (exists_pos_pow_mem H σ) ⟨hm, h⟩

section FrobPower

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

private theorem mk_pow_smul_of_isArithFrobAt {σ : G} {Q : Ideal B} (hF : IsArithFrobAt A σ Q) (n : ℕ) (x : B) :
    Ideal.Quotient.mk Q (σ ^ n • x) = Ideal.Quotient.mk Q x ^ (Nat.card (A ⧸ Q.under A) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hx : Ideal.Quotient.mk Q (σ • x) = Ideal.Quotient.mk Q x ^ Nat.card (A ⧸ Q.under A) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact hF x
    rw [pow_succ, mul_smul, ih (σ • x), hx, ← pow_mul, pow_succ']

variable [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_card_pow_eq_self_of_pow_mem {H : Subgroup G} [SMulCommClass (↥H) C B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {n : ℕ} (hmem : arithFrobAt A G Q ^ n ∈ H) (y : C ⧸ Q.under C) :
    y ^ (Nat.card (A ⧸ Q.under A) ^ n) = y := by
  have hF : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfix : (arithFrobAt A G Q ^ n) • algebraMap C B c = algebraMap C B c := by
    have h : (⟨arithFrobAt A G Q ^ n, hmem⟩ : ↥H) • algebraMap C B c = algebraMap C B c := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    exact h
  have hq := mk_pow_smul_of_isArithFrobAt hF n (algebraMap C B c)
  rw [hfix] at hq
  rw [← map_pow, Ideal.Quotient.eq, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow, ← Ideal.Quotient.eq,
    map_pow]
  exact hq.symm

private theorem pow_arithFrobAt_mem_of_card_under_eq_pow {H : Subgroup G} [SMulCommClass (↥H) C B]
    [Algebra.IsInvariant C B (↥H)] (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {f : ℕ}
    (hcard : Nat.card (C ⧸ Q.under C) = Nat.card (A ⧸ Q.under A) ^ f) (hin : Q.inertia G = ⊥) :
    arithFrobAt A G Q ^ f ∈ H := by
  obtain ⟨s, hs⟩ := IsArithFrobAt.exists_of_isInvariant C (↥H) Q
  have hτ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  have key : ∀ x : B, (arithFrobAt A G Q ^ f) • x - (s : G) • x ∈ Q := by
    intro x
    have h1 := mk_pow_smul_of_isArithFrobAt hτ f x
    have h2 : (s : G) • x - x ^ (Nat.card (A ⧸ Q.under A) ^ f) ∈ Q := by
      have h := hs x
      rwa [hcard] at h
    rw [← Ideal.Quotient.eq, map_pow] at h2
    rw [← Ideal.Quotient.eq, h1, h2]
  have hmem : arithFrobAt A G Q ^ f * (s : G)⁻¹ ∈ Q.inertia G := by
    intro x
    have h := key ((s : G)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hin, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact s.2

end FrobPower

open Polynomial in

private theorem card_le_of_forall_pow_eq {R : Type*} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : R, y ^ q = y) : Nat.card R ≤ q := by
  classical
  haveI := Fintype.ofFinite R
  have hdeg : (X ^ q - X : R[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    rw [natDegree_X]
    exact hq
  have hf0 : (X ^ q - X : R[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroots : ∀ y : R, y ∈ (X ^ q - X : R[X]).roots := fun y =>
    (mem_roots hf0).2 (by simp [h y])
  calc Nat.card R = Fintype.card R := Nat.card_eq_fintype_card
    _ ≤ (X ^ q - X : R[X]).roots.toFinset.card :=
        Finset.card_le_card fun y _ => Multiset.mem_toFinset.2 (hroots y)
    _ ≤ Multiset.card (X ^ q - X : R[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : R[X]).natDegree := card_roots' _
    _ = q := hdeg

section Places

variable {K : Type} [Field K] [NumberField K]

private theorem exists_char_card (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ ∃ m : ℕ, 0 < m ∧ Nat.card (𝓞 K ⧸ w.asIdeal) = ℓ ^ m := by
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI : Fintype (𝓞 K ⧸ w.asIdeal) := Fintype.ofFinite _
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), hp, ?_, (n : ℕ), n.pos, by rw [Nat.card_eq_fintype_card, hcard]⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar (𝓞 K ⧸ w.asIdeal))

private theorem under_int_eq (w : HeightOneSpectrum (𝓞 K)) {ℓ : ℕ} (hℓ : ℓ.Prime) (hw : ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.under ℤ = ratPrimeIdeal ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ((Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_).symm
  show Ideal.span {((ℓ : ℕ) : ℤ)} ≤ w.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hw

private theorem finite_setOf_mem (ℓ : ℕ) (hℓ : ℓ.Prime) :
    {w : HeightOneSpectrum (𝓞 K) | ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal}.Finite := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  apply Set.Finite.of_finite_image (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
    (hi := fun x _ y _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
  apply Set.Finite.subset (IsDedekindDomain.primesOver_finite (ratPrimeIdeal ℓ) (𝓞 K))
  rintro I ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨(under_int_eq w hℓ hw).symm⟩⟩

private theorem finite_guarded (ℓ : ℕ) :
    {w : HeightOneSpectrum (𝓞 K) | ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal}.Finite := by
  by_cases hℓ : ℓ.Prime
  · exact (finite_setOf_mem ℓ hℓ).subset fun w hw => hw.2
  · convert Set.finite_empty
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hℓ h.1

private theorem finite_bad (T : Finset ℕ) :
    {w : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ T, ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal}.Finite := by
  have hsub : {w : HeightOneSpectrum (𝓞 K) | ∃ ℓ ∈ T, ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal}
      ⊆ ⋃ ℓ ∈ T, {w : HeightOneSpectrum (𝓞 K) | ℓ.Prime ∧ ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal} := fun w hw => by
    obtain ⟨ℓ, hℓT, hℓ, hw⟩ := hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨ℓ, hℓT, hℓ, hw⟩
  exact Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun ℓ _ => finite_guarded ℓ) hsub

private theorem card_int_quot (ℓ : ℕ) : Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

end Places

section Tower

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

private theorem tower_isGaloisGroup (H : Subgroup (L ≃ₐ[ℚ] L)) :
    IsGaloisGroup (↥H) (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing _ _ _ (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) L

private theorem card_residue_eq_pow_relDeg (H : Subgroup (L ≃ₐ[ℚ] L))
    (w : HeightOneSpectrum (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hQℓ : (primeOver H w).LiesOver (ratPrimeIdeal ℓ))
    (hI : (primeOver H w).inertia (L ≃ₐ[ℚ] L) = ⊥) {m : ℕ} (hm : 0 < m)
    (hcard : Nat.card (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) ⧸ w.asIdeal) = ℓ ^ m) :
    m = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)) := by
  classical
  have hGG := tower_isGaloisGroup H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  have hw : w.asIdeal = (primeOver H w).under (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))) :=
    (under_primeOver H w).symm
  have hcardZ : Nat.card (ℤ ⧸ (primeOver H w).under ℤ) = ℓ := by
    rw [← hQℓ.over]
    exact card_int_quot ℓ
  have hℓ1 : 1 < ℓ := hℓ.one_lt
  set n := relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)) with hn

  have hle : m ≤ n := by
    haveI : w.asIdeal.IsMaximal := w.isMaximal
    letI : Field (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) ⧸ w.asIdeal) :=
      Ideal.Quotient.field _
    haveI : Finite (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) ⧸ w.asIdeal) :=
      Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
    have hpow : ∀ y : 𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) ⧸ w.asIdeal,
        y ^ (ℓ ^ n) = y := by
      rw [hw]
      intro y
      have h := pow_card_pow_eq_self_of_pow_mem (A := ℤ)
        (C := 𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))) (H := H) (primeOver H w)
        (relDeg_spec H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w))).2 y
      rwa [hcardZ] at h
    have h1lt : 1 < ℓ ^ n := Nat.one_lt_pow (relDeg_spec H _).1.ne' hℓ1
    have hcle := card_le_of_forall_pow_eq h1lt hpow
    rw [hcard] at hcle
    exact (Nat.pow_le_pow_iff_right hℓ1).mp hcle

  have hge : n ≤ m := by
    have hcard' : Nat.card (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)) ⧸
        (primeOver H w).under (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))))
        = Nat.card (ℤ ⧸ (primeOver H w).under ℤ) ^ m := by
      rw [hcardZ, ← hw, hcard]
    exact relDeg_le H _ hm (pow_arithFrobAt_mem_of_card_under_eq_pow (A := ℤ)
      (C := 𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))) (H := H) (primeOver H w) hcard' hI)
  exact le_antisymm hle hge

private theorem red_det_seed (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (H : Subgroup (L ≃ₐ[ℚ] L)) (hdet : DetDictionaryRow e)
    (w : HeightOneSpectrum (𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L))))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hQℓ : (primeOver H w).LiesOver (ratPrimeIdeal ℓ))
    (hI : (primeOver H w).inertia (L ≃ₐ[ℚ] L) = ⊥) :
    red (liftOf (e (seedFrob H w))).det = (ℓ : ZMod 3) ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)) := by
  have hd := hdet ℓ hℓ hℓ3 (primeOver H w) inferInstance hQℓ inferInstance hI
  rw [RingHom.map_det, RingHom.mapMatrix_apply, (liftOf_spec _).2, seedFrob, map_pow, Units.val_pow_eq_pow_val,
    Matrix.det_pow, hd]

end Tower

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (H : Subgroup (L ≃ₐ[ℚ] L))
    (hdet : DetDictionaryRow e) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(FixedPoints.intermediateField H : IntermediateField ℚ L))), ∀ v ∉ S,
      (P2.liftTraceSeed e H).b v = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)) := by
  obtain ⟨B, hB⟩ := exists_finset_forall_inertia_eq_bot L
  refine ⟨(finite_bad (insert 3 B)).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv
  obtain ⟨ℓ, hℓ, hℓv, m, hm, hcard⟩ := exists_char_card v
  have hℓT : ℓ ∉ insert 3 B := fun h => hv ⟨ℓ, h, hℓ, hℓv⟩
  have hℓ3 : ℓ ≠ 3 := fun h => hℓT (by rw [h]; exact Finset.mem_insert_self 3 B)
  have hℓB : ℓ ∉ B := fun h => hℓT (Finset.mem_insert_of_mem h)
  have hQℓ : (primeOver H v).LiesOver (ratPrimeIdeal ℓ) := by
    constructor
    rw [← Ideal.under_under (A := ℤ) (B := 𝓞 (↥(FixedPoints.intermediateField H : IntermediateField ℚ L)))
      (C := 𝓞 L), under_primeOver, under_int_eq v hℓ hℓv]
  have hI := hB hℓ hℓB (primeOver H v) inferInstance hQℓ
  have hmn := card_residue_eq_pow_relDeg H v hℓ hQℓ hI hm hcard
  have hred := red_det_seed e H hdet v hℓ hℓ3 hQℓ hI

  have hnorm : Ideal.absNorm v.asIdeal = ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H v)) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hmn]
    exact hcard

  have hchi : ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ZMod 3)
      = (ℓ : ZMod 3) ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H v)) := by
    have h := FLT.OccurrenceStatement.three_dvd_natCast_sub_chiNegThree_cast (ZMod 3) (Ideal.absNorm v.asIdeal)
    rw [show (3 : ZMod 3) = 0 by decide, zero_dvd_iff, sub_eq_zero] at h
    rw [← h, hnorm, Nat.cast_pow]
  have hM := det_liftOf (e (seedFrob H v))
  have hredχ : red (liftOf (e (seedFrob H v))).det
      = red ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)) := by
    rw [map_intCast, hchi, hred]

  have hχ : ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)) = 1 ∨
      ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)) = -1 := by
    rcases chiNegThree_cases (Ideal.absNorm v.asIdeal) with h | h | h
    · left; rw [h]; simp
    · right; rw [h]; simp
    · exfalso
      rw [h] at hredχ
      simp only [Int.cast_zero, map_zero] at hredχ
      rcases hM with hM | hM <;> rw [hM] at hredχ
      · simp only [map_one] at hredχ
        exact absurd hredχ (by decide)
      · simp only [map_neg, map_one] at hredχ
        exact absurd hredχ (by decide)
  exact eq_of_pm1_of_red_eq hM hχ hredχ

end S_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow
end P2MW
export P2MW.S_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow (solution)
