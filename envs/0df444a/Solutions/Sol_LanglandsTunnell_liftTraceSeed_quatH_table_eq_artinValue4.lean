-- Prove2me | solution 1 for LanglandsTunnell.liftTraceSeed_quatH_table_eq_artinValue4
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/eeebcae4-9028-5787-9f17-8235711a4598

import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_Lift48
import Theorems.Thm_LanglandsTunnell_exists_finset_forall_inertia_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_liftTraceSeed_quatH_table_eq_artinValue4

set_option autoImplicit false
set_option Elab.async false

open NumberField IsDedekindDomain AutomorphicForm
open LanglandsTunnell LanglandsTunnell.P2 LanglandsTunnell.Lift48 FLT.ExplicitLift FrobeniusDensity
open scoped Pointwise

local notation "M₃" => Matrix (Fin 2) (Fin 2) (ZMod 3)

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

private theorem nodup_map_redc_K48 : (K48.map fun k => k.map redc).Nodup := by decide +kernel

private theorem lift_unique_K48 {M N : Mat} (hM : M ∈ Submonoid.closure ({Slift, Tlift} : Set Mat))
    (hN : N ∈ Submonoid.closure ({Slift, Tlift} : Set Mat)) (h : M.map red = N.map red) : M = N :=
  List.inj_on_of_nodup_map nodup_map_redc_K48 ((mem_closure_iff_mem_K48 M).1 hM) ((mem_closure_iff_mem_K48 N).1 hN)
    (by rwa [map_red_eq_map_redc, map_red_eq_map_redc] at h)

private theorem liftOf_mul' (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    liftOf (g * h) = liftOf g * liftOf h :=
  lift_unique_K48 (liftOf_spec _).1 (Submonoid.mul_mem _ (liftOf_spec _).1 (liftOf_spec _).1)
    (by rw [Matrix.map_mul, (liftOf_spec _).2, (liftOf_spec _).2, (liftOf_spec _).2, Units.val_mul])

private theorem liftOf_one' : liftOf (1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 1 :=
  lift_unique_K48 (liftOf_spec _).1 (Submonoid.one_mem _)
    (by rw [(liftOf_spec _).2, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)])

private theorem liftOf_pow' (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : ∀ n : ℕ, liftOf (g ^ n) = liftOf g ^ n
  | 0 => by rw [pow_zero, pow_zero, liftOf_one']
  | (n + 1) => by rw [pow_succ, pow_succ, liftOf_mul', liftOf_pow' g n]

private theorem liftOf_inv_mul' (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : liftOf g⁻¹ * liftOf g = 1 := by
  rw [← liftOf_mul', inv_mul_cancel, liftOf_one']

private theorem liftOf_mul_inv' (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : liftOf g * liftOf g⁻¹ = 1 := by
  rw [← liftOf_mul', mul_inv_cancel, liftOf_one']

private theorem trace_liftOf_conj' (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (liftOf (g * h * g⁻¹)).trace = (liftOf h).trace := by
  rw [liftOf_mul', liftOf_mul', Matrix.trace_mul_cycle, liftOf_inv_mul', one_mul]

private theorem det_liftOf_conj' (g h : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (liftOf (g * h * g⁻¹)).det = (liftOf h).det := by
  rw [liftOf_mul', liftOf_mul', Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, liftOf_mul_inv',
    Matrix.det_one, one_mul]

private theorem liftOf_eq_of_red {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)} {M : Mat} (hM : M ∈ K48)
    (h : M.map red = (g : M₃)) : liftOf g = M :=
  lift_unique_K48 (liftOf_spec g).1 ((mem_closure_iff_mem_K48 M).2 hM) (by rw [(liftOf_spec g).2, h])

private theorem Q8_sub_K48 : ∀ M ∈ Q8, M ∈ K48 := by decide
private theorem P16_sub_K48 : ∀ M ∈ P16, M ∈ K48 := by decide

private def inv2 (x : Mat) : Mat := !![det2 x * x 1 1, -(det2 x * x 0 1); -(det2 x * x 1 0), det2 x * x 0 0]
private theorem Q8_mul_inv2 : ∀ x ∈ Q8, x * inv2 x = 1 ∧ inv2 x ∈ Q8 := by decide

private theorem C4_quadratic : ∀ a ∈ Q8, ∀ b ∈ Q8, a ∉ C4 → b ∉ C4 → a * b ∈ C4 := by decide

private theorem C4_conj_inv2 : ∀ x ∈ Q8, ∀ c ∈ C4, x * c * inv2 x ∈ C4 ∧ (x ∉ C4 → x * c * inv2 x = pw c 3) := by
  decide

private theorem Q8_off_C4 : ∀ g ∈ Q8, g ∉ C4 → tr2 g = 0 ∧ det2 g = 1 ∧ g * g = pw Tlift 4 := by decide
private theorem Q8_det2 : ∀ g ∈ Q8, det2 g = 1 := by decide

private theorem mem_Q8_of_redc_det2 : ∀ g ∈ P16, redc (det2 g) = 1 → g ∈ Q8 := by decide
private theorem C4_sub_C8 : ∀ c ∈ C4, c ∈ C8 := by decide
private theorem even_of_pw_mem_C4 : ∀ n ∈ List.range 8, pw Tlift n ∈ C4 → n % 2 = 0 := by decide

private def log4 (k : Mat) : ℕ := C4.idxOf k

private theorem log4_table :
    (∀ j ∈ List.range 4, pw Tlift (2 * j) ∈ C4 ∧ log4 (pw Tlift (2 * j)) = j) ∧
    (∀ c ∈ C4, log4 c < 4 ∧ pw c 3 ∈ C4 ∧ log4 (pw c 3) = 3 * log4 c % 4 ∧ det2 c = 1 ∧ pw Tlift (2 * log4 c) = c) ∧
    pw Tlift 4 ∈ C4 ∧ log4 (pw Tlift 4) = 2 := by
  decide

private theorem tr2_C4_table :
    tr2 (pw Tlift 0) = 2 ∧ tr2 (pw Tlift 2) = 0 ∧ tr2 (pw Tlift 4) = -2 ∧ tr2 (pw Tlift 6) = 0 := by
  decide

private theorem Tlift_pow_two_mul (k : ℕ) : Tlift ^ (2 * k) = pw Tlift (2 * (k % 4)) := by
  have hk : 2 * k = 8 * (k / 4) + 2 * (k % 4) := by omega
  rw [pw_eq_pow, hk, pow_add, pow_mul, Tlift_pow_eight_eq_one, one_pow, one_mul]

private def psi4 (ζ : ℂ) (k : Mat) : ℂ := if k ∈ C4 then ζ ^ (2 * log4 k) else 0

private theorem psi4_of_mem (ζ : ℂ) {k : Mat} (hk : k ∈ C4) : psi4 ζ k = ζ ^ (2 * log4 k) := by
  rw [psi4, if_pos hk]

private theorem zeta_pow_two_mul {ζ : ℂ} (hζ : ζ ^ 4 = -1) (k : ℕ) : ζ ^ (2 * k) = ζ ^ (2 * (k % 4)) := by
  have hk : 2 * k = 8 * (k / 4) + 2 * (k % 4) := by omega
  rw [hk, pow_add, pow_mul, zeta_pow_eight hζ, one_pow, one_mul]

private theorem zeta_pow_six {ζ : ℂ} (hζ : ζ ^ 4 = -1) : ζ ^ 6 = -ζ ^ 2 := by
  calc ζ ^ 6 = ζ ^ 4 * ζ ^ 2 := by ring
    _ = -ζ ^ 2 := by rw [hζ]; ring

private theorem psi4_Tlift_two_mul {ζ : ℂ} (hζ : ζ ^ 4 = -1) (k : ℕ) :
    psi4 ζ (Tlift ^ (2 * k)) = ζ ^ (2 * k) := by
  have hlt : k % 4 ∈ List.range 4 := List.mem_range.2 (Nat.mod_lt _ (by norm_num))
  obtain ⟨hmem, hlog⟩ := log4_table.1 (k % 4) hlt
  rw [Tlift_pow_two_mul, psi4_of_mem ζ hmem, hlog, zeta_pow_two_mul hζ k]

private theorem induced_trace_C4 {ζ : ℂ} (hζ : ζ ^ 4 = -1) {g x : Mat} (hg : g ∈ C4) (hx : x ∈ Q8)
    (hxC : x ∉ C4) : iotaZsqrtdNegTwo (tr2 g) = psi4 ζ g + psi4 ζ (x * g * inv2 x) := by
  rw [(C4_conj_inv2 x hx g hg).2 hxC]
  obtain ⟨hl, hg3, hlog3, -, hpw⟩ := log4_table.2.1 g hg
  have htr : tr2 g = tr2 (pw Tlift (2 * log4 g)) := by rw [hpw]
  rw [htr, psi4_of_mem ζ hg, psi4_of_mem ζ hg3, hlog3]
  obtain ⟨h0, h2, h4, h6⟩ := tr2_C4_table
  have hz6 := zeta_pow_six hζ
  generalize log4 g = l at hl ⊢
  interval_cases l
  · try rw [show (2 * 0 : ℕ) = 0 from rfl]
    rw [h0, map_ofNat]
    norm_num
  · try rw [show (2 * 1 : ℕ) = 2 from rfl]
    rw [h2, map_zero]
    norm_num [hz6]
  · try rw [show (2 * 2 : ℕ) = 4 from rfl]
    rw [h4, map_neg, map_ofNat]
    norm_num [hζ]
  · try rw [show (2 * 3 : ℕ) = 6 from rfl]
    rw [h6, map_zero]
    norm_num [hz6]

private theorem induced_det_C4 {ζ : ℂ} (hζ : ζ ^ 4 = -1) {g x : Mat} (hg : g ∈ C4) (hx : x ∈ Q8)
    (hxC : x ∉ C4) : iotaZsqrtdNegTwo (det2 g) = psi4 ζ g * psi4 ζ (x * g * inv2 x) := by
  rw [(C4_conj_inv2 x hx g hg).2 hxC]
  obtain ⟨hl, hg3, hlog3, hdet, -⟩ := log4_table.2.1 g hg
  rw [hdet, map_one, psi4_of_mem ζ hg, psi4_of_mem ζ hg3, hlog3, ← pow_add]
  have h8 := zeta_pow_eight hζ
  generalize log4 g = l at hl ⊢
  interval_cases l <;> norm_num [h8]

private theorem induced_inert_Q8 {ζ : ℂ} (hζ : ζ ^ 4 = -1) {g : Mat} (hg : g ∈ Q8) (hgC : g ∉ C4) :
    tr2 g = 0 ∧ iotaZsqrtdNegTwo (det2 g) = -psi4 ζ (g * g) := by
  obtain ⟨htr, hdet, hsq⟩ := Q8_off_C4 g hg hgC
  refine ⟨htr, ?_⟩
  obtain ⟨h4, hlog4⟩ := log4_table.2.2
  rw [hdet, map_one, hsq, psi4_of_mem ζ h4, hlog4, show (2 * 2 : ℕ) = 4 from rfl, hζ, neg_neg]

private theorem chiGal4_pow_eq {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) (k : ℕ) :
    LanglandsTunnell.P2.chiGal4 e hζ (LanglandsTunnell.P2.gammaTSqMem e ^ k) =
      LanglandsTunnell.P2.zetaUnit hζ ^ (2 * k) := by
  rw [map_pow, LanglandsTunnell.P2.chiGal4_gammaTSqMem, ← pow_mul]

private theorem exists_gammaTSq_pow_eq {L : Type} [Field L] [NumberField L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (x : ↥(LanglandsTunnell.P2.c4H e)) :
    ∃ k : ℕ, k < 4 ∧ LanglandsTunnell.P2.gammaTSqMem e ^ k = x := by
  have hfin : IsOfFinOrder (LanglandsTunnell.P2.gammaTSqMem e) := by
    rw [← orderOf_pos_iff, LanglandsTunnell.P2.orderOf_gammaTSqMem]
    norm_num
  have hx : x ∈ Submonoid.powers (LanglandsTunnell.P2.gammaTSqMem e) :=
    hfin.mem_powers_iff_mem_zpowers.mpr (LanglandsTunnell.P2.mem_zpowers_gammaTSqMem e x)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hx
  refine ⟨n % 4, Nat.mod_lt _ (by norm_num), ?_⟩
  have h := pow_mod_orderOf (LanglandsTunnell.P2.gammaTSqMem e) n
  rw [LanglandsTunnell.P2.orderOf_gammaTSqMem] at h
  rw [h, hn]

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

omit [NumberField K] in

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

end Tower

section Bridges

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

private theorem liftOf_mem_P16 {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ sylowH e) : liftOf (e γ) ∈ P16 := by
  obtain ⟨M, hM, hred⟩ := (mem_sylowH_iff e γ).1 hγ
  rw [liftOf_eq_of_red (P16_sub_K48 M hM) hred]
  exact hM

private theorem mem_sylowH_of_liftOf {γ : L ≃ₐ[ℚ] L} (h : liftOf (e γ) ∈ P16) : γ ∈ sylowH e :=
  (mem_sylowH_iff e γ).2 ⟨_, h, (liftOf_spec _).2⟩

private theorem mem_c8H_of_liftOf {γ : L ≃ₐ[ℚ] L} (h : liftOf (e γ) ∈ C8) : γ ∈ c8H e :=
  (mem_c8H_iff e γ).2 ⟨_, h, (liftOf_spec _).2⟩

private theorem liftOf_gammaT_pow (k : ℕ) : liftOf (e (gammaT e ^ k)) = Tlift ^ k := by
  rw [map_pow, e_gammaT, liftOf_pow']
  congr 1
  exact liftOf_eq_of_red Tlift_mem_K48 (by rw [val_tbarGL, RingHom.mapMatrix_apply])

private theorem liftOf_mem_Q8 {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ quatH e) : liftOf (e γ) ∈ Q8 := by
  have hP : liftOf (e γ) ∈ P16 := liftOf_mem_P16 e (quatH_le_sylowH e hγ)
  have hdet := (mem_detKer_iff e γ).1 (quatH_le_detKer e hγ)
  refine mem_Q8_of_redc_det2 _ hP ?_
  rw [← red_eq_redc, det2_eq_det, RingHom.map_det, RingHom.mapMatrix_apply, (liftOf_spec (e γ)).2]
  exact hdet

private theorem mem_quatH_of_liftOf {γ : L ≃ₐ[ℚ] L} (h : liftOf (e γ) ∈ Q8) : γ ∈ quatH e := by
  show γ ∈ sylowH e ⊓ detKer e
  refine Subgroup.mem_inf.2 ⟨mem_sylowH_of_liftOf e (Q8_sub_P16 _ h), (mem_detKer_iff e γ).2 ?_⟩
  rw [← (liftOf_spec (e γ)).2, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← det2_eq_det, Q8_det2 _ h, map_one]

private theorem val_gammaTSqMem_pow (k : ℕ) :
    ((gammaTSqMem e ^ k : ↥(c4H e)) : L ≃ₐ[ℚ] L) = gammaT e ^ (2 * k) := by
  rw [pow_mul]
  rfl

private theorem liftOf_mem_C4 {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ c4H e) : liftOf (e γ) ∈ C4 := by
  obtain ⟨k, -, hk⟩ := exists_gammaTSq_pow_eq e ⟨γ, hγ⟩
  have hγ' : gammaT e ^ (2 * k) = γ := (val_gammaTSqMem_pow e k).symm.trans (congrArg Subtype.val hk)
  rw [← hγ', liftOf_gammaT_pow, Tlift_pow_two_mul]
  exact (log4_table.1 (k % 4) (List.mem_range.2 (Nat.mod_lt k (by norm_num)))).1

private theorem mem_c4H_of_liftOf {γ : L ≃ₐ[ℚ] L} (h : liftOf (e γ) ∈ C4) : γ ∈ c4H e := by
  obtain ⟨k, hk⟩ := exists_pow_gammaT_eq e (mem_c8H_of_liftOf e (C4_sub_C8 _ h))
  rw [← hk, liftOf_gammaT_pow] at h
  have h1 : Tlift ^ k = Tlift ^ (8 * (k / 8) + k % 8) := by rw [Nat.div_add_mod]
  have h2 : Tlift ^ k = pw Tlift (k % 8) := by
    rw [pw_eq_pow, h1, pow_add, pow_mul, Tlift_pow_eight_eq_one, one_pow, one_mul]
  rw [h2] at h
  have heven := even_of_pw_mem_C4 (k % 8) (List.mem_range.2 (Nat.mod_lt k (by norm_num))) h
  rw [← hk, mem_c4H_iff]
  refine ⟨((k / 2 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← pow_mul]
  congr 1
  omega

private theorem liftOf_inv_eq_inv2 {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ quatH e) :
    liftOf (e σ⁻¹) = inv2 (liftOf (e σ)) := by
  have hQ := liftOf_mem_Q8 e hσ
  obtain ⟨h1, h7⟩ := Q8_mul_inv2 _ hQ
  refine liftOf_eq_of_red (Q8_sub_K48 _ h7) ?_
  rw [map_inv]
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← (liftOf_spec (e σ)).2, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero red) (map_one red)]

private theorem liftOf_conj_eq {σ γ : L ≃ₐ[ℚ] L} (hσ : σ ∈ quatH e) :
    liftOf (e (σ * γ * σ⁻¹)) = liftOf (e σ) * liftOf (e γ) * inv2 (liftOf (e σ)) := by
  rw [map_mul, map_mul, liftOf_mul', liftOf_mul', liftOf_inv_eq_inv2 e hσ]

private theorem conj_mem_c4H {σ γ : L ≃ₐ[ℚ] L} (hσ : σ ∈ quatH e) (hγ : γ ∈ c4H e) : σ * γ * σ⁻¹ ∈ c4H e := by
  apply mem_c4H_of_liftOf e
  rw [liftOf_conj_eq e hσ]
  exact (C4_conj_inv2 _ (liftOf_mem_Q8 e hσ) _ (liftOf_mem_C4 e hγ)).1

private theorem conj_mem_c4H_iff {σ γ : L ≃ₐ[ℚ] L} (hσ : σ ∈ quatH e) : σ * γ * σ⁻¹ ∈ c4H e ↔ γ ∈ c4H e := by
  refine ⟨fun h => ?_, conj_mem_c4H e hσ⟩
  have h' := conj_mem_c4H e ((quatH e).inv_mem hσ) h
  have hγ : σ⁻¹ * (σ * γ * σ⁻¹) * σ⁻¹⁻¹ = γ := by group
  rwa [hγ] at h'

private theorem mul_mem_c4H_of_not_mem {a b : L ≃ₐ[ℚ] L} (ha : a ∈ quatH e) (hb : b ∈ quatH e)
    (haC : a ∉ c4H e) (hbC : b ∉ c4H e) : a * b ∈ c4H e := by
  apply mem_c4H_of_liftOf e
  rw [map_mul, liftOf_mul']
  exact C4_quadratic _ (liftOf_mem_Q8 e ha) _ (liftOf_mem_Q8 e hb) (fun h => haC (mem_c4H_of_liftOf e h))
    (fun h => hbC (mem_c4H_of_liftOf e h))

variable {ζ : ℂ} (hζ : ζ ^ 4 = -1)

private theorem val_chiGal4_eq_psi4 (γ : L ≃ₐ[ℚ] L) (hγ : γ ∈ c4H e) :
    ((chiGal4 e hζ ⟨γ, hγ⟩ : ℂˣ) : ℂ) = psi4 ζ (liftOf (e γ)) := by
  obtain ⟨k, -, hk⟩ := exists_gammaTSq_pow_eq e ⟨γ, hγ⟩
  have hγ' : gammaT e ^ (2 * k) = γ := (val_gammaTSqMem_pow e k).symm.trans (congrArg Subtype.val hk)
  rw [← hk, chiGal4_pow_eq, Units.val_pow_eq_pow_val, val_zetaUnit, ← hγ', liftOf_gammaT_pow,
    psi4_Tlift_two_mul hζ]

end Bridges

section Frobenius

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in

private theorem inertia_smul_eq_bot' (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : 𝓞 L, g • x - x ∈ τ • Q := fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem arithFrobAt_of_smul_eq (τ : L ≃ₐ[ℚ] L) (Q₀ Q : Ideal (𝓞 L)) [Q₀.IsPrime] [Finite (𝓞 L ⧸ Q₀)]
    [Q.IsPrime] [Finite (𝓞 L ⧸ Q)] (h : τ • Q₀ = Q) (hI : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ * τ⁻¹ := by
  subst h
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q₀)) (τ • Q₀) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q₀)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ * τ⁻¹) (τ • Q₀) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot' τ Q₀ hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

private theorem pow_arithFrobAt_smul (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)] (n : ℕ) :
    (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ n) • Q = Q :=
  MulAction.mem_stabilizer_iff.1
    ((MulAction.stabilizer (L ≃ₐ[ℚ] L) Q).pow_mem (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).mem_stabilizer n)

private theorem relDeg_eq_of_forall_iff {G : Type*} [Group G] [Finite G] (H : Subgroup G) {σ σ' : G}
    (h : ∀ m : ℕ, σ' ^ m ∈ H ↔ σ ^ m ∈ H) : relDeg H σ' = relDeg H σ :=
  le_antisymm (relDeg_le H _ (relDeg_spec H σ).1 ((h _).2 (relDeg_spec H σ).2))
    (relDeg_le H _ (relDeg_spec H σ').1 ((h _).1 (relDeg_spec H σ').2))

end Frobenius

section IntTower

variable {L : Type} [Field L] [NumberField L]

private theorem ringOfIntegers_isScalarTower (E K : IntermediateField ℚ L) [Algebra ↥E ↥K]
    [IsScalarTower ↥E ↥K L] : IsScalarTower (𝓞 ↥E) (𝓞 ↥K) (𝓞 L) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  apply IsFractionRing.injective (𝓞 L) L
  rw [← IsScalarTower.algebraMap_apply (𝓞 ↥E) (𝓞 L) L, ← IsScalarTower.algebraMap_apply (𝓞 ↥K) (𝓞 L) L,
    IsScalarTower.algebraMap_apply (𝓞 ↥E) ↥E L, IsScalarTower.algebraMap_apply (𝓞 ↥K) ↥K L,
    ← IsScalarTower.algebraMap_apply (𝓞 ↥E) (𝓞 ↥K) ↥K, IsScalarTower.algebraMap_apply (𝓞 ↥E) ↥E ↥K,
    ← IsScalarTower.algebraMap_apply ↥E ↥K L]

private theorem card_quot_eq_pow_inertiaDeg {E K : Type*} [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (𝔓 : HeightOneSpectrum (𝓞 K)) [𝔓.asIdeal.LiesOver v.asIdeal] :
    Nat.card (𝓞 K ⧸ 𝔓.asIdeal) = Nat.card (𝓞 E ⧸ v.asIdeal) ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 E ⧸ v.asIdeal)]

end IntTower

section Dictionary

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

private theorem seed_eq_at (v : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e))))
    (hI₀ : (primeOver (quatH e) v).inertia (L ≃ₐ[ℚ] L) = ⊥)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)] (hQv : Q.under (𝓞 ↥(fixFld (quatH e))) = v.asIdeal) :
    relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
        = relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v)) ∧
      (P2.liftTraceSeed e (quatH e)).a v
        = (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)))).trace ∧
      (P2.liftTraceSeed e (quatH e)).b v
        = (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)))).det := by
  haveI hGG := tower_isGaloisGroup (L := L) (quatH e)
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : (primeOver (quatH e) v).LiesOver v.asIdeal := ⟨(under_primeOver (quatH e) v).symm⟩
  haveI : Q.LiesOver v.asIdeal := ⟨hQv.symm⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeOver (quatH e) v) Q ↥(quatH e)
  have hτ' : (τ : L ≃ₐ[ℚ] L) • primeOver (quatH e) v = Q := hτ
  have hF := arithFrobAt_of_smul_eq (τ : L ≃ₐ[ℚ] L) (primeOver (quatH e) v) Q hτ' hI₀
  have hrel : relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
      = relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v)) := by
    rw [hF]
    refine relDeg_eq_of_forall_iff (quatH e) fun m => ?_
    rw [conj_pow]
    refine ⟨fun h => ?_, fun h => (quatH e).mul_mem ((quatH e).mul_mem τ.2 h) ((quatH e).inv_mem τ.2)⟩
    have h' := (quatH e).mul_mem ((quatH e).mul_mem ((quatH e).inv_mem τ.2) h) τ.2
    have hγ : (τ : L ≃ₐ[ℚ] L)⁻¹ * ((τ : L ≃ₐ[ℚ] L) * arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v) ^ m
        * (τ : L ≃ₐ[ℚ] L)⁻¹) * (τ : L ≃ₐ[ℚ] L) = arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v) ^ m := by
      group
    rwa [hγ] at h'
  refine ⟨hrel, ?_, ?_⟩
  · show (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v)
      ^ relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v))))).trace = _
    rw [hrel, hF, conj_pow, map_mul, map_mul, map_inv, trace_liftOf_conj']
  · show (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v)
      ^ relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (quatH e) v))))).det = _
    rw [hrel, hF, conj_pow, map_mul, map_mul, map_inv, det_liftOf_conj']

private theorem relDeg_c4H_eq (F : L ≃ₐ[ℚ] L) :
    (F ^ relDeg (quatH e) F ∈ c4H e → relDeg (c4H e) F = relDeg (quatH e) F) ∧
    (F ^ relDeg (quatH e) F ∉ c4H e → relDeg (c4H e) F = 2 * relDeg (quatH e) F) := by
  obtain ⟨hn, hmem⟩ := relDeg_spec (quatH e) F
  have hle : relDeg (quatH e) F ≤ relDeg (c4H e) F :=
    relDeg_le (quatH e) F (relDeg_spec (c4H e) F).1 (c4H_le_quatH e (relDeg_spec (c4H e) F).2)
  refine ⟨fun h => le_antisymm (relDeg_le (c4H e) F hn h) hle, fun h => ?_⟩

  have h2n : F ^ (2 * relDeg (quatH e) F) ∈ c4H e := by
    rw [two_mul, pow_add]
    exact mul_mem_c4H_of_not_mem e hmem hmem h h
  have hup : relDeg (c4H e) F ≤ 2 * relDeg (quatH e) F := relDeg_le (c4H e) F (by omega) h2n
  obtain ⟨hn', hmem'⟩ := relDeg_spec (c4H e) F

  have hr : F ^ (relDeg (c4H e) F % relDeg (quatH e) F) ∈ quatH e := by
    have hq : F ^ relDeg (c4H e) F = (F ^ relDeg (quatH e) F) ^ (relDeg (c4H e) F / relDeg (quatH e) F)
        * F ^ (relDeg (c4H e) F % relDeg (quatH e) F) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h1 : F ^ relDeg (c4H e) F ∈ quatH e := c4H_le_quatH e hmem'
    rw [hq] at h1
    have h2 : (F ^ relDeg (quatH e) F) ^ (relDeg (c4H e) F / relDeg (quatH e) F) ∈ quatH e :=
      (quatH e).pow_mem hmem _
    have h3 := (quatH e).mul_mem ((quatH e).inv_mem h2) h1
    rwa [inv_mul_cancel_left] at h3
  have hr0 : relDeg (c4H e) F % relDeg (quatH e) F = 0 := by
    by_contra hne
    have hpos : 0 < relDeg (c4H e) F % relDeg (quatH e) F := Nat.pos_of_ne_zero hne
    have := relDeg_le (quatH e) F hpos hr
    have hlt : relDeg (c4H e) F % relDeg (quatH e) F < relDeg (quatH e) F := Nat.mod_lt _ hn
    omega
  obtain ⟨q, hq⟩ : relDeg (quatH e) F ∣ relDeg (c4H e) F := Nat.dvd_of_mod_eq_zero hr0

  have hq1 : q ≠ 1 := by
    rintro rfl
    rw [mul_one] at hq
    rw [← hq] at h
    exact h hmem'
  have hq2 : relDeg (quatH e) F * q ≤ relDeg (quatH e) F * 2 := by rw [← hq, mul_comm]; exact hup
  have hq2' : q ≤ 2 := Nat.le_of_mul_le_mul_left hq2 hn
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    omega
  have hq22 : q = 2 := by omega
  rw [hq, hq22, mul_comm]

omit [IsGalois ℚ L] in

private theorem primeOver_c4H_under_eq (v : HeightOneSpectrum (𝓞 ↥(fixFld (quatH e))))
    (𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e)))) (h𝔓 : 𝔓.under (𝓞 ↥(fixFld (quatH e))) = v) :
    (primeOver (c4H e) 𝔓).under (𝓞 ↥(fixFld (quatH e))) = v.asIdeal := by
  haveI := ringOfIntegers_isScalarTower (L := L) (fixFld (quatH e)) (fixFld (P2.c4H e))
  rw [← Ideal.under_under (B := 𝓞 ↥(fixFld (P2.c4H e))), under_primeOver, ← h𝔓]
  rfl

end Dictionary

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (quatH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e))), 𝔓₁ ≠ 𝔓₂ →
          𝔓₁.under (𝓞 ↥(fixFld (quatH e))) = v → 𝔓₂.under (𝓞 ↥(fixFld (quatH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).a v) =
            (P2.artinValue4 e hζ 𝔓₁ : ℂ) + P2.artinValue4 e hζ 𝔓₂ ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) =
            (P2.artinValue4 e hζ 𝔓₁ : ℂ) * P2.artinValue4 e hζ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e))), 𝔓.under (𝓞 ↥(fixFld (quatH e))) = v →
          v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (quatH e)).a v = 0 ∧
          iotaZsqrtdNegTwo ((P2.liftTraceSeed e (quatH e)).b v) = -(P2.artinValue4 e hζ 𝔓 : ℂ)) := by

  classical
  obtain ⟨B, hB⟩ := exists_finset_forall_inertia_eq_bot L
  refine ⟨(finite_bad B).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv

  obtain ⟨ℓ, hℓ, hℓv, m, hm, hcard⟩ := exists_char_card v
  have hℓB : ℓ ∉ B := fun h => hv ⟨ℓ, h, hℓ, hℓv⟩
  haveI := ringOfIntegers_isScalarTower (L := L) (fixFld (quatH e)) (fixFld (P2.c4H e))
  haveI hGG := tower_isGaloisGroup (L := L) (quatH e)
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  haveI hGG' := tower_isGaloisGroup (L := L) (c4H e)
  haveI := hGG'.commutes
  haveI := hGG'.isInvariant

  have hQ₀ℓ : (primeOver (quatH e) v).LiesOver (ratPrimeIdeal ℓ) := by
    constructor
    rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(fixFld (quatH e))) (C := 𝓞 L), under_primeOver, under_int_eq v hℓ hℓv]
  have hI₀ := hB hℓ hℓB (primeOver (quatH e) v) inferInstance hQ₀ℓ
  have hmn := card_residue_eq_pow_relDeg (quatH e) v hℓ hQ₀ℓ hI₀ hm hcard

  have key : ∀ 𝔓 : HeightOneSpectrum (𝓞 ↥(fixFld (P2.c4H e))), 𝔓.under (𝓞 ↥(fixFld (quatH e))) = v →
      (primeOver (c4H e) 𝔓).inertia (L ≃ₐ[ℚ] L) = ⊥ ∧
      (primeOver (c4H e) 𝔓).under (𝓞 ↥(fixFld (quatH e))) = v.asIdeal ∧
      relDeg (quatH e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓)) = m ∧
      (P2.liftTraceSeed e (quatH e)).a v
        = (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m))).trace ∧
      (P2.liftTraceSeed e (quatH e)).b v
        = (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m))).det ∧
      Nat.card (𝓞 ↥(fixFld (P2.c4H e)) ⧸ 𝔓.asIdeal)
        = ℓ ^ relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓)) := by
    intro 𝔓 h𝔓
    have hQv := primeOver_c4H_under_eq e v 𝔓 h𝔓
    have hQℓ : (primeOver (c4H e) 𝔓).LiesOver (ratPrimeIdeal ℓ) := by
      constructor
      rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(fixFld (quatH e))) (C := 𝓞 L), hQv, under_int_eq v hℓ hℓv]
    have hI := hB hℓ hℓB (primeOver (c4H e) 𝔓) inferInstance hQℓ
    obtain ⟨hrel, ha, hb⟩ := seed_eq_at e v hI₀ (primeOver (c4H e) 𝔓) hQv
    rw [← hmn] at hrel
    rw [hrel] at ha hb
    refine ⟨hI, hQv, hrel, ha, hb, ?_⟩

    obtain ⟨ℓ', hℓ', hℓ'𝔓, m', hm', hcard'⟩ := exists_char_card 𝔓
    have hℓℓ : ℓ' = ℓ := by
      have h1 := under_int_eq 𝔓 hℓ' hℓ'𝔓
      have h2 : 𝔓.asIdeal.under ℤ = ratPrimeIdeal ℓ := by
        rw [← under_primeOver (c4H e) 𝔓, Ideal.under_under]
        exact hQℓ.over.symm
      rw [h1] at h2
      have h3 : ((ℓ' : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := by
        rw [← h2]
        exact Ideal.mem_span_singleton_self _
      rw [ratPrimeIdeal, Ideal.mem_span_singleton] at h3
      exact (Nat.prime_dvd_prime_iff_eq hℓ hℓ').1 (Int.natCast_dvd_natCast.1 h3) |>.symm
    subst hℓℓ
    rw [hcard', card_residue_eq_pow_relDeg (c4H e) 𝔓 hℓ' hQℓ hI hm' hcard']
  refine ⟨?_, ?_⟩
  ·
    intro 𝔓₁ 𝔓₂ hne h₁ h₂
    obtain ⟨hI₁, hQ₁v, hn₁, ha, hb, -⟩ := key 𝔓₁ h₁
    obtain ⟨hI₂, hQ₂v, hn₂, -, -, -⟩ := key 𝔓₂ h₂
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    haveI : (primeOver (c4H e) 𝔓₁).LiesOver v.asIdeal := ⟨hQ₁v.symm⟩
    haveI : (primeOver (c4H e) 𝔓₂).LiesOver v.asIdeal := ⟨hQ₂v.symm⟩

    obtain ⟨σ, hσ⟩ :=
      Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeOver (c4H e) 𝔓₁) (primeOver (c4H e) 𝔓₂) ↥(quatH e)
    have hσ' : (σ : L ≃ₐ[ℚ] L) • primeOver (c4H e) 𝔓₁ = primeOver (c4H e) 𝔓₂ := hσ
    have hσH : (σ : L ≃ₐ[ℚ] L) ∈ quatH e := σ.2
    have hFσ : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₂)
        = (σ : L ≃ₐ[ℚ] L) * arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) * (σ : L ≃ₐ[ℚ] L)⁻¹ :=
      arithFrobAt_of_smul_eq _ (primeOver (c4H e) 𝔓₁) (primeOver (c4H e) 𝔓₂) hσ' hI₁

    have hunderC : ∀ c : L ≃ₐ[ℚ] L, c ∈ c4H e →
        (c • primeOver (c4H e) 𝔓₁).under (𝓞 ↥(fixFld (P2.c4H e))) = 𝔓₁.asIdeal := fun c hc =>
      (Ideal.under_smul (𝓞 ↥(fixFld (P2.c4H e))) (primeOver (c4H e) 𝔓₁) (⟨c, hc⟩ : ↥(c4H e))).trans
        (under_primeOver (c4H e) 𝔓₁)

    have hg₁ : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m ∈ c4H e := by
      by_contra hg
      apply hne
      have hQ₂under : (primeOver (c4H e) 𝔓₂).under (𝓞 ↥(fixFld (P2.c4H e))) = 𝔓₁.asIdeal := by
        by_cases hσC : (σ : L ≃ₐ[ℚ] L) ∈ c4H e
        · rw [← hσ']
          exact hunderC _ hσC
        · have hmemH : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m ∈ quatH e := by
            rw [← hn₁]
            exact (relDeg_spec (quatH e) _).2
          have hc : (σ : L ≃ₐ[ℚ] L) * (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m)⁻¹ ∈ c4H e :=
            mul_mem_c4H_of_not_mem e hσH ((quatH e).inv_mem hmemH) hσC
              (fun h => hg (by simpa using (c4H e).inv_mem h))
          have hfix : (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m) • primeOver (c4H e) 𝔓₁
              = primeOver (c4H e) 𝔓₁ := pow_arithFrobAt_smul _ m
          have hfix' : (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m)⁻¹ • primeOver (c4H e) 𝔓₁
              = primeOver (c4H e) 𝔓₁ := inv_smul_eq_iff.2 hfix.symm
          have hσQ : (σ : L ≃ₐ[ℚ] L) • primeOver (c4H e) 𝔓₁
              = ((σ : L ≃ₐ[ℚ] L) * (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m)⁻¹)
                  • primeOver (c4H e) 𝔓₁ := by
            rw [mul_smul, hfix']
          rw [← hσ', hσQ]
          exact hunderC _ hc
      exact HeightOneSpectrum.ext (by rw [← hQ₂under]; exact under_primeOver (c4H e) 𝔓₂)

    have hσC : (σ : L ≃ₐ[ℚ] L) ∉ c4H e := by
      intro hσC
      apply hne
      exact HeightOneSpectrum.ext (by rw [← under_primeOver (c4H e) 𝔓₂, ← hσ', hunderC _ hσC])

    have hrel₁ : relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁)) = m := by
      rw [← hn₁]
      exact (relDeg_c4H_eq e _).1 (by rw [hn₁]; exact hg₁)
    have hrel₂ : relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₂)) = m := by
      rw [← hrel₁, hFσ]
      exact relDeg_eq_of_forall_iff (c4H e) fun k => by rw [conj_pow]; exact conj_mem_c4H_iff e hσH
    have hval₁ : (P2.artinValue4 e hζ 𝔓₁ : ℂ)
        = psi4 ζ (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m))) := by
      rw [artinValue4_def, val_chiGal4_eq_psi4 e hζ]
      show psi4 ζ (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁)
        ^ relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁))))) = _
      rw [hrel₁]
    have hval₂ : (P2.artinValue4 e hζ 𝔓₂ : ℂ)
        = psi4 ζ (liftOf (e (σ : L ≃ₐ[ℚ] L)) * liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m))
            * inv2 (liftOf (e (σ : L ≃ₐ[ℚ] L)))) := by
      rw [artinValue4_def, val_chiGal4_eq_psi4 e hζ]
      show psi4 ζ (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₂)
        ^ relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₂))))) = _
      rw [hrel₂, hFσ, conj_pow, liftOf_conj_eq e hσH]
    have hG₁ : liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓₁) ^ m)) ∈ C4 := liftOf_mem_C4 e hg₁
    have hx : liftOf (e (σ : L ≃ₐ[ℚ] L)) ∈ Q8 := liftOf_mem_Q8 e hσH
    have hxC : liftOf (e (σ : L ≃ₐ[ℚ] L)) ∉ C4 := fun h => hσC (mem_c4H_of_liftOf e h)
    refine ⟨?_, ?_⟩
    · rw [ha, hval₁, hval₂, ← tr2_eq_trace]
      exact induced_trace_C4 hζ hG₁ hx hxC
    · rw [hb, hval₁, hval₂, ← det2_eq_det]
      exact induced_det_C4 hζ hG₁ hx hxC
  ·
    intro 𝔓 h𝔓 hf
    obtain ⟨hI, hQv, hn, ha, hb, hcard𝔓⟩ := key 𝔓 h𝔓

    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h𝔓]; rfl⟩
    have hcc := card_quot_eq_pow_inertiaDeg v 𝔓
    rw [hcard𝔓, hcard, hf, ← pow_mul] at hcc
    have h2 : relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓)) = m * 2 :=
      Nat.pow_right_injective hℓ.two_le hcc

    have hg : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m ∉ c4H e := by
      intro h
      have h1 := (relDeg_c4H_eq e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓))).1 (by rw [hn]; exact h)
      rw [hn] at h1
      omega
    have hGP : liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m)) ∈ Q8 :=
      liftOf_mem_Q8 e (by rw [← hn]; exact (relDeg_spec (quatH e) _).2)
    have hGC : liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m)) ∉ C4 :=
      fun h => hg (mem_c4H_of_liftOf e h)
    have hval : (P2.artinValue4 e hζ 𝔓 : ℂ)
        = psi4 ζ (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m))
            * liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓) ^ m))) := by
      rw [artinValue4_def, val_chiGal4_eq_psi4 e hζ]
      show psi4 ζ (liftOf (e (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓)
        ^ relDeg (c4H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) 𝔓))))) = _
      rw [h2, pow_mul, pow_two, map_mul, liftOf_mul']
    obtain ⟨htr0, hdet0⟩ := induced_inert_Q8 hζ hGP hGC
    refine ⟨?_, ?_⟩
    · rw [ha, ← tr2_eq_trace]
      exact htr0
    · rw [hb, hval, ← det2_eq_det]
      exact hdet0

end S_LanglandsTunnell_liftTraceSeed_quatH_table_eq_artinValue4
end P2MW
export P2MW.S_LanglandsTunnell_liftTraceSeed_quatH_table_eq_artinValue4 (solution)
