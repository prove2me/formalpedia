-- Prove2me | solution 1 for ModularCurve.two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/9cb42db0-f325-5376-a2fd-53c5e781e30c

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo
import Theorems.Thm_ZMod_natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix MatrixGroups CongruenceSubgroup MulAction

noncomputable section

namespace EllipticCount

section Lift

private lemma natCast_dvd_int {p : ℕ} {z : ℤ} : (p : ℤ) ∣ z ↔ p ∣ z.natAbs :=
  Int.natCast_dvd

private def primeSel (c d : ℤ) : ℕ :=
  ∏ p ∈ c.natAbs.primeFactors, if p ∣ d.natAbs then 1 else p

private lemma dvd_primeSel {c d : ℤ} {p : ℕ} (hc : c ≠ 0) (hp : p.Prime)
    (hpc : (p : ℤ) ∣ c) (hpd : ¬(p : ℤ) ∣ d) : p ∣ primeSel c d := by
  have hmem : p ∈ c.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, natCast_dvd_int.mp hpc, Int.natAbs_ne_zero.mpr hc⟩
  have h := Finset.dvd_prod_of_mem (fun q : ℕ => if q ∣ d.natAbs then 1 else q) hmem
  simp only [if_neg (fun hcontra => hpd (natCast_dvd_int.mpr hcontra))] at h
  exact h

private lemma not_dvd_primeSel {c d : ℤ} {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ d) :
    ¬p ∣ primeSel c d := by
  intro hdvd
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_finsetProd_iff _ |>.mp hdvd
  by_cases hqd : q ∣ d.natAbs
  · rw [if_pos hqd] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  · rw [if_neg hqd] at hpq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    exact hqd (((Nat.prime_dvd_prime_iff_eq hp hq').mp hpq) ▸ natCast_dvd_int.mp hpd)

theorem exists_coprime_lift (N : ℕ) [NeZero N] {c₀ d₀ : ℤ}
    (H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ c₀ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ)) :
    ∃ γ δ : ℤ, Int.gcd γ δ = 1 ∧
      (γ : ZMod N) = (c₀ : ZMod N) ∧ (δ : ZMod N) = (d₀ : ZMod N) := by
  set γ : ℤ := if c₀ = 0 then (N : ℤ) else c₀ with hγ_def
  have hγ0 : γ ≠ 0 := by
    rw [hγ_def]; split
    · exact_mod_cast NeZero.ne N
    · assumption
  have hγc : (γ : ZMod N) = (c₀ : ZMod N) := by
    rw [hγ_def]; split
    · next h => rw [h]; simp
    · rfl
  have Hγ : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ γ → (p : ℤ) ∣ d₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpγ hpd hpN
    rw [hγ_def] at hpγ
    split at hpγ
    · next h =>
      refine H p pp ?_ hpd hpN
      rw [h]; exact dvd_zero _
    · exact H p pp hpγ hpd hpN
  refine ⟨γ, d₀ + primeSel γ d₀ * N, ?_, hγc, ?_⟩
  · by_contra hne
    obtain ⟨p, pp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : (p : ℤ) ∣ γ :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
    have h2 : (p : ℤ) ∣ d₀ + (primeSel γ d₀ : ℤ) * (N : ℤ) :=
      natCast_dvd_int.mpr (hpdvd.trans (Nat.gcd_dvd_right _ _))
    by_cases hpd : (p : ℤ) ∣ d₀
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) * (N : ℤ) := by
        have := h2.sub hpd; rwa [add_sub_cancel_left] at this
      have h3' : p ∣ primeSel γ d₀ * N := by
        have : (p : ℤ) ∣ ((primeSel γ d₀ * N : ℕ) : ℤ) := by push_cast; exact h3
        exact_mod_cast this
      rcases (pp.prime.dvd_mul.mp h3') with h4 | h4
      · exact not_dvd_primeSel pp hpd h4
      · exact Hγ p pp h1 hpd (by exact_mod_cast h4)
    · have h3 : (p : ℤ) ∣ (primeSel γ d₀ : ℤ) :=
        natCast_dvd_int.mpr (dvd_primeSel hγ0 pp h1 hpd)
      refine hpd ?_
      have := h2.sub (h3.mul_right (N : ℤ)); rwa [add_sub_cancel_right] at this
  · push_cast; simp

end Lift

variable (N : ℕ) [NeZero N]

abbrev V : Type := ZMod N × ZMod N

abbrev red (g : SL(2, ℤ)) : SL(2, ZMod N) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g

theorem red_apply (g : SL(2, ℤ)) (i j : Fin 2) : red N g i j = ((g i j : ℤ) : ZMod N) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

def col (g : SL(2, ℤ)) : V N := (red N g 0 0, red N g 1 0)

def lineOf (g : SL(2, ℤ)) : AddSubgroup (V N) := AddSubgroup.zmultiples (col N g)

theorem col_mul (g h : SL(2, ℤ)) :
    col N (g * h) = red N h 0 0 • col N g + red N h 1 0 • (red N g 0 1, red N g 1 1) := by
  have hm : red N (g * h) = red N g * red N h := map_mul _ g h
  unfold col
  have e00 : red N (g * h) 0 0 = red N g 0 0 * red N h 0 0 + red N g 0 1 * red N h 1 0 := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : red N (g * h) 1 0 = red N g 1 0 * red N h 0 0 + red N g 1 1 * red N h 1 0 := by
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine Prod.ext ?_ ?_
  · show red N (g * h) 0 0 = red N h 0 0 * red N g 0 0 + red N h 1 0 * red N g 0 1
    rw [e00]; ring
  · show red N (g * h) 1 0 = red N h 0 0 * red N g 1 0 + red N h 1 0 * red N g 1 1
    rw [e10]; ring

theorem exists_combo_eq_one (g : SL(2, ℤ)) :
    ∃ x y : ZMod N, x * red N g 0 0 + y * red N g 1 0 = 1 := by
  refine ⟨red N g 1 1, -red N g 0 1, ?_⟩
  have hdet := Matrix.SpecialLinearGroup.det_coe (red N g)
  rw [Matrix.det_fin_two] at hdet
  linear_combination hdet

theorem natCast_smul_eq_zero (v : V N) : (N : ℤ) • v = 0 := by
  ext <;> simp

theorem addOrderOf_col (g : SL(2, ℤ)) : addOrderOf (col N g) = N := by
  obtain ⟨x, y, hxy⟩ := exists_combo_eq_one N g
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    have := natCast_smul_eq_zero N (col N g)
    rwa [natCast_zsmul] at this
  · have h := addOrderOf_nsmul_eq_zero (col N g)
    set d := addOrderOf (col N g)
    have h1 : (d : ZMod N) * red N g 0 0 = 0 := by
      have := congrArg Prod.fst h; simpa [col, nsmul_eq_mul] using this
    have h2 : (d : ZMod N) * red N g 1 0 = 0 := by
      have := congrArg Prod.snd h; simpa [col, nsmul_eq_mul] using this
    have hd : (d : ZMod N) = 0 := by
      have : (d : ZMod N) = (d : ZMod N) * (x * red N g 0 0 + y * red N g 1 0) := by rw [hxy, mul_one]
      rw [this]; linear_combination x * h1 + y * h2
    exact (CharP.cast_eq_zero_iff (ZMod N) N d).mp hd

theorem natCard_lineOf (g : SL(2, ℤ)) : Nat.card (lineOf N g) = N := by
  rw [lineOf, Nat.card_zmultiples, addOrderOf_col]

theorem isAddCyclic_lineOf (g : SL(2, ℤ)) : IsAddCyclic (lineOf N g) := by
  unfold lineOf; infer_instance

theorem smul_mem_of_mem (L : AddSubgroup (V N)) (r : ZMod N) {v : V N} (hv : v ∈ L) : r • v ∈ L := by
  have : r • v = r.val • v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod N) r.val v, ZMod.natCast_zmod_val]
  rw [this]
  exact AddSubgroup.nsmul_mem _ hv _

theorem lineOf_mul_of_mem {g : SL(2, ℤ)} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    lineOf N (g * γ) = lineOf N g := by
  have hc : red N γ 1 0 = 0 := by rw [red_apply]; exact Gamma0_mem.mp hγ
  have hcol : col N (g * γ) = red N γ 0 0 • col N g := by
    rw [col_mul, hc, zero_smul, add_zero]
  have hunit : red N γ 1 1 * red N γ 0 0 = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe (red N γ)
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    rw [mul_comm]; exact hdet
  apply le_antisymm
  · rw [lineOf, AddSubgroup.zmultiples_le, hcol]
    exact smul_mem_of_mem N _ _ (AddSubgroup.mem_zmultiples _)
  · rw [lineOf, AddSubgroup.zmultiples_le]
    have : col N g = red N γ 1 1 • col N (g * γ) := by
      rw [hcol, smul_smul, hunit, one_smul]
    rw [this]
    exact smul_mem_of_mem N _ _ (AddSubgroup.mem_zmultiples _)

def lineQ : SL(2, ℤ) ⧸ Gamma0 N → AddSubgroup (V N) :=
  Quotient.lift (lineOf N) fun a b h => by
    have h' : a⁻¹ * b ∈ Gamma0 N := QuotientGroup.leftRel_apply.mp h
    have : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
    rw [this, lineOf_mul_of_mem N h']

theorem lineQ_mk (g : SL(2, ℤ)) : lineQ N (g : SL(2, ℤ) ⧸ Gamma0 N) = lineOf N g := rfl

theorem lineQ_injective : Function.Injective (lineQ N) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H g =>
  induction y using QuotientGroup.induction_on with | H g' =>
  rw [lineQ_mk, lineQ_mk] at hxy
  have hmem : col N g' ∈ lineOf N g := by rw [hxy]; exact AddSubgroup.mem_zmultiples _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem

  set γ := g⁻¹ * g' with hγ
  have hg' : g' = g * γ := by rw [hγ, mul_inv_cancel_left]
  rw [hg', col_mul] at hk

  apply QuotientGroup.eq.mpr
  show γ ∈ Gamma0 N
  rw [Gamma0_mem, ← red_apply]

  have hdet := Matrix.SpecialLinearGroup.det_coe (red N g)
  rw [Matrix.det_fin_two] at hdet
  simp only [col, Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq, smul_eq_mul, zsmul_eq_mul] at hk
  obtain ⟨e1, e2⟩ := hk
  have key : red N γ 1 0 * (red N g 0 0 * red N g 1 1 - red N g 0 1 * red N g 1 0) = 0 := by
    linear_combination red N g 1 0 * e1 - red N g 0 0 * e2
  rw [hdet, mul_one] at key
  exact key

theorem exists_lineOf_eq (L : AddSubgroup (V N)) (hcyc : IsAddCyclic L) (hcard : Nat.card L = N) :
    ∃ g : SL(2, ℤ), lineOf N g = L := by

  obtain ⟨⟨v, hvL⟩, hv⟩ := hcyc.exists_generator
  have hL : L = AddSubgroup.zmultiples v := by
    apply le_antisymm
    · intro w hw
      obtain ⟨k, hk⟩ := hv ⟨w, hw⟩
      exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [AddSubgroup.zmultiples_le]; exact hvL
  have hord : addOrderOf v = N := by rw [← Nat.card_zmultiples, ← hL, hcard]

  obtain ⟨a, c⟩ := v
  set a₀ : ℤ := (a.cast : ℤ) with ha₀
  set c₀ : ℤ := (c.cast : ℤ) with hc₀
  have hca : ((a₀ : ℤ) : ZMod N) = a := ZMod.intCast_zmod_cast a
  have hcc : ((c₀ : ℤ) : ZMod N) = c := ZMod.intCast_zmod_cast c

  have H : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a₀ → (p : ℤ) ∣ c₀ → ¬(p : ℤ) ∣ (N : ℤ) := by
    intro p pp hpa hpc hpN
    obtain ⟨a₁, ha₁⟩ := hpa
    obtain ⟨c₁, hc₁⟩ := hpc
    obtain ⟨M, hM⟩ : (p : ℕ) ∣ N := by exact_mod_cast hpN
    have hM0 : M ≠ 0 := by rintro rfl; exact NeZero.ne N (by simpa using hM)
    have hsmul : M • ((a, c) : V N) = 0 := by
      have hMN : (M : ZMod N) * (p : ZMod N) = 0 := by
        rw [← Nat.cast_mul, mul_comm, ← hM]; exact ZMod.natCast_self N
      ext
      · show M • a = 0
        rw [← hca, ha₁, nsmul_eq_mul]; push_cast
        linear_combination (a₁ : ZMod N) * hMN
      · show M • c = 0
        rw [← hcc, hc₁, nsmul_eq_mul]; push_cast
        linear_combination (c₁ : ZMod N) * hMN
    have hdvd : N ∣ M := by rw [← hord]; exact addOrderOf_dvd_of_nsmul_eq_zero hsmul
    have hle : p * M ≤ M := by rw [← hM]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hdvd
    have hMpos := Nat.pos_of_ne_zero hM0
    nlinarith [pp.one_lt]
  obtain ⟨α, γ, hcop, hα, hγ⟩ := exists_coprime_lift N H
  rw [hca] at hα; rw [hcc] at hγ

  set x : ℤ := Int.gcdA α γ
  set y : ℤ := Int.gcdB α γ
  have hbez : α * x + γ * y = 1 := by
    have h := Int.gcd_eq_gcd_ab α γ
    rw [hcop] at h; push_cast at h
    linear_combination -h
  refine ⟨⟨!![α, -y; γ, x], by rw [Matrix.det_fin_two_of]; linear_combination hbez⟩, ?_⟩
  rw [hL, lineOf]
  congr 1
  unfold col
  ext
  · rw [red_apply]; simpa using hα
  · rw [red_apply]; simpa using hγ

def lineEquiv : SL(2, ℤ) ⧸ Gamma0 N ≃ {L : AddSubgroup (V N) // IsAddCyclic L ∧ Nat.card L = N} where
  toFun x := ⟨lineQ N x, by
    induction x using QuotientGroup.induction_on with | H g =>
    exact ⟨isAddCyclic_lineOf N g, natCard_lineOf N g⟩⟩
  invFun L := ((exists_lineOf_eq N L.1 L.2.1 L.2.2).choose : SL(2, ℤ) ⧸ Gamma0 N)
  left_inv x := by
    induction x using QuotientGroup.induction_on with | H g =>
    apply lineQ_injective
    rw [lineQ_mk, lineQ_mk]
    exact (exists_lineOf_eq N (lineOf N g) (isAddCyclic_lineOf N g) (natCard_lineOf N g)).choose_spec
  right_inv L := by
    apply Subtype.ext
    exact (exists_lineOf_eq N L.1 L.2.1 L.2.2).choose_spec

theorem lineEquiv_mk (g : SL(2, ℤ)) : ((lineEquiv N (g : SL(2, ℤ) ⧸ Gamma0 N)) : AddSubgroup (V N)) = lineOf N g :=
  rfl

def τS : V N →+ V N where
  toFun v := (-v.2, v.1)
  map_zero' := by simp
  map_add' v w := by ext <;> simp <;> try ring

def τST : V N →+ V N where
  toFun v := (-v.2, v.1 + v.2)
  map_zero' := by simp
  map_add' v w := by ext <;> simp <;> try ring

theorem col_S_mul (g : SL(2, ℤ)) : col N (ModularGroup.S * g) = τS N (col N g) := by
  have hm : red N (ModularGroup.S * g) = red N ModularGroup.S * red N g := map_mul _ _ g
  have hS : ∀ i j, red N ModularGroup.S i j = ((ModularGroup.S i j : ℤ) : ZMod N) := red_apply N _
  unfold col τS
  ext
  · show red N (ModularGroup.S * g) 0 0 = -red N g 1 0
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hS, ModularGroup.S]
  · show red N (ModularGroup.S * g) 1 0 = red N g 0 0
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hS, ModularGroup.S]

theorem col_ST_mul (g : SL(2, ℤ)) : col N (ModularGroup.S * ModularGroup.T * g) = τST N (col N g) := by
  have hm : red N (ModularGroup.S * ModularGroup.T * g) = red N (ModularGroup.S * ModularGroup.T) * red N g :=
    map_mul _ _ g
  have hST : ModularGroup.S * ModularGroup.T = ⟨!![0, -1; 1, 1], by decide⟩ := by decide
  have hS : ∀ i j, red N (ModularGroup.S * ModularGroup.T) i j
      = (((ModularGroup.S * ModularGroup.T) i j : ℤ) : ZMod N) := red_apply N _
  unfold col τST
  ext
  · show red N (ModularGroup.S * ModularGroup.T * g) 0 0 = -red N g 1 0
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hS, hST]
  · show red N (ModularGroup.S * ModularGroup.T * g) 1 0 = red N g 0 0 + red N g 1 0
    rw [hm, Matrix.SpecialLinearGroup.coe_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hS, hST]

theorem lineOf_S_mul (g : SL(2, ℤ)) : lineOf N (ModularGroup.S * g) = (lineOf N g).map (τS N) := by
  rw [lineOf, lineOf, col_S_mul, AddMonoidHom.map_zmultiples]

theorem lineOf_ST_mul (g : SL(2, ℤ)) :
    lineOf N (ModularGroup.S * ModularGroup.T * g) = (lineOf N g).map (τST N) := by
  rw [lineOf, lineOf, col_ST_mul, AddMonoidHom.map_zmultiples]

def fixedEquiv (A : SL(2, ℤ)) (τ : V N →+ V N) (hτ : ∀ g, lineOf N (A * g) = (lineOf N g).map τ) :
    fixedBy (SL(2, ℤ) ⧸ Gamma0 N) A
      ≃ {L : AddSubgroup (V N) // IsAddCyclic L ∧ Nat.card L = N ∧ L.map τ = L} where
  toFun x := ⟨(lineEquiv N x.1).1, (lineEquiv N x.1).2.1, (lineEquiv N x.1).2.2, by
    obtain ⟨x, hx⟩ := x
    induction x using QuotientGroup.induction_on with | H g =>
    have hx' : ((A * g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 N) = (g : SL(2, ℤ) ⧸ Gamma0 N) := hx
    have := congrArg (lineQ N) hx'
    rw [lineQ_mk, lineQ_mk, hτ] at this
    exact this⟩
  invFun L := ⟨(lineEquiv N).symm ⟨L.1, L.2.1, L.2.2.1⟩, by
    have key : ∀ x : SL(2, ℤ) ⧸ Gamma0 N, (lineEquiv N x).1 = L.1 → A • x = x := by
      intro x hx
      induction x using QuotientGroup.induction_on with | H g =>
      apply lineQ_injective
      show lineOf N (A * g) = lineOf N g
      have hx' : lineOf N g = L.1 := hx
      rw [hτ, hx']
      exact L.2.2.2
    exact key _ (by rw [Equiv.apply_symm_apply])⟩
  left_inv x := by
    apply Subtype.ext
    exact (lineEquiv N).symm_apply_apply x.1
  right_inv L := by
    apply Subtype.ext
    show (lineEquiv N ((lineEquiv N).symm ⟨L.1, L.2.1, L.2.2.1⟩)).1 = L.1
    rw [Equiv.apply_symm_apply]

end EllipticCount

namespace EllipticCount

variable (N : ℕ) [NeZero N]

abbrev X : Type := SL(2, ℤ) ⧸ Gamma0 N

theorem neg_one_mem_Gamma0 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]; simp

theorem neg_one_smul (x : X N) : (-1 : SL(2, ℤ)) • x = x := by
  induction x using QuotientGroup.induction_on with | H g =>
  show (((-1 : SL(2, ℤ)) * g : SL(2, ℤ)) : X N) = (g : X N)
  rw [neg_one_mul, ← mul_neg_one]
  exact QuotientGroup.mk_mul_of_mem g (neg_one_mem_Gamma0 N)

theorem fixedBy_mul_of_trivial (A B : SL(2, ℤ)) (hB : ∀ x : X N, B • x = x) :
    fixedBy (X N) (A * B) = fixedBy (X N) A := by
  ext x
  simp only [MulAction.mem_fixedBy, mul_smul, hB]

theorem fixedBy_sq_of_cube (A : SL(2, ℤ)) (hA : ∀ x : X N, A ^ 3 • x = x) :
    fixedBy (X N) (A ^ 2) = fixedBy (X N) A := by
  ext x
  simp only [MulAction.mem_fixedBy]
  constructor
  · intro h
    have h3 := hA x
    rw [pow_succ', mul_smul, h] at h3
    exact h3
  · intro h
    rw [sq, mul_smul, h, h]

theorem natCard_fixedBy_one : Nat.card (fixedBy (X N) (1 : SL(2, ℤ))) = Nat.card (X N) := by
  rw [MulAction.fixedBy_one_eq_univ]
  exact Nat.card_congr (Equiv.Set.univ _)

theorem natCard_X : Nat.card (X N) = ModularCurve.dedekindPsi N := by
  rw [← ModularCurve.Gamma0_index N, Subgroup.index]

theorem burnside (A : SL(2, ℤ)) (n : ℕ) (hn : 0 < n) (hord : orderOf A = n) :
    ∑ k ∈ Finset.range n, Nat.card (fixedBy (X N) (A ^ k))
      = n * Nat.card (orbitRel.Quotient (Subgroup.zpowers A) (X N)) := by
  classical
  have hfin : IsOfFinOrder A := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← hord, pow_orderOf_eq_one]⟩
  haveI : Finite (Subgroup.zpowers A) := Finite.of_equiv _ (finEquivZPowers hfin)
  haveI : Fintype (Subgroup.zpowers A) := Fintype.ofFinite _
  haveI : Fintype (X N) := Fintype.ofFinite _
  haveI : ∀ a : Subgroup.zpowers A, Fintype (fixedBy (X N) a) := fun _ => Fintype.ofFinite _
  haveI : Fintype (Quotient (orbitRel (Subgroup.zpowers A) (X N))) := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (Subgroup.zpowers A) (X N)
  simp only [Fintype.card_eq_nat_card] at hB
  rw [Nat.card_zpowers, hord, mul_comm] at hB
  rw [← hB]

  have hsum : ∑ a : Subgroup.zpowers A, Nat.card (fixedBy (X N) a)
      = ∑ k : Fin (orderOf A), Nat.card (fixedBy (X N) (A ^ (k : ℕ))) := by
    refine (Fintype.sum_equiv (finEquivZPowers hfin) _ _ fun k => ?_).symm
    rw [finEquivZPowers_apply]
    rfl
  rw [hsum, ← Fin.sum_univ_eq_sum_range, hord]

theorem orderOf_S : orderOf ModularGroup.S = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem orderOf_ST : orderOf (ModularGroup.S * ModularGroup.T) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

theorem S_sq_smul (x : X N) : ModularGroup.S ^ 2 • x = x := by
  rw [show ModularGroup.S ^ 2 = -1 by decide]; exact neg_one_smul N x

theorem ST_cube_smul (x : X N) : (ModularGroup.S * ModularGroup.T) ^ 3 • x = x := by
  rw [show (ModularGroup.S * ModularGroup.T) ^ 3 = -1 by decide]; exact neg_one_smul N x

theorem two_mul_card_orbits_S :
    2 * Nat.card (orbitRel.Quotient (Subgroup.zpowers ModularGroup.S) (X N))
      = Nat.card (X N) + Nat.card (fixedBy (X N) ModularGroup.S) := by
  have hB := burnside N ModularGroup.S 4 (by norm_num) orderOf_S
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hB
  have h2 : fixedBy (X N) (ModularGroup.S ^ 2) = fixedBy (X N) (1 : SL(2, ℤ)) := by
    ext x; simp only [MulAction.mem_fixedBy, S_sq_smul, one_smul]
  have h3 : fixedBy (X N) (ModularGroup.S ^ 3) = fixedBy (X N) ModularGroup.S := by
    rw [pow_succ', sq]
    rw [show ModularGroup.S * (ModularGroup.S * ModularGroup.S) = ModularGroup.S * ModularGroup.S ^ 2 by rw [sq]]
    exact fixedBy_mul_of_trivial N _ _ (S_sq_smul N)
  rw [h2, h3, natCard_fixedBy_one] at hB
  omega

theorem three_mul_card_orbits_ST :
    3 * Nat.card (orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T)) (X N))
      = Nat.card (X N) + 2 * Nat.card (fixedBy (X N) (ModularGroup.S * ModularGroup.T)) := by
  have hB := burnside N (ModularGroup.S * ModularGroup.T) 6 (by norm_num) orderOf_ST
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at hB
  have h2 : fixedBy (X N) ((ModularGroup.S * ModularGroup.T) ^ 2) = fixedBy (X N) (ModularGroup.S * ModularGroup.T) := fixedBy_sq_of_cube N (ModularGroup.S * ModularGroup.T) (ST_cube_smul N)
  have h3 : fixedBy (X N) ((ModularGroup.S * ModularGroup.T) ^ 3) = fixedBy (X N) (1 : SL(2, ℤ)) := by
    ext x; simp only [MulAction.mem_fixedBy, ST_cube_smul, one_smul]
  have h4 : fixedBy (X N) ((ModularGroup.S * ModularGroup.T) ^ 4) = fixedBy (X N) (ModularGroup.S * ModularGroup.T) := by
    rw [show (ModularGroup.S * ModularGroup.T) ^ 4 = (ModularGroup.S * ModularGroup.T) * (ModularGroup.S * ModularGroup.T) ^ 3 by rw [pow_succ']]
    exact fixedBy_mul_of_trivial N _ _ (ST_cube_smul N)
  have h5 : fixedBy (X N) ((ModularGroup.S * ModularGroup.T) ^ 5) = fixedBy (X N) (ModularGroup.S * ModularGroup.T) := by
    rw [show (ModularGroup.S * ModularGroup.T) ^ 5 = (ModularGroup.S * ModularGroup.T) ^ 2 * (ModularGroup.S * ModularGroup.T) ^ 3 by rw [← pow_add]]
    rw [fixedBy_mul_of_trivial N _ _ (ST_cube_smul N), h2]
  rw [h2, h3, h4, h5, natCard_fixedBy_one] at hB
  omega

theorem natCast_M_ne_zero {p M : ℕ} (hp : p.Prime) (hM : N = p * M) (hMpos : 0 < M) : (M : ZMod N) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (ZMod N) N] at h
  have hle := Nat.le_of_dvd hMpos h
  rw [hM] at hle
  nlinarith [hp.one_lt]

theorem addOrderOf_test {p M : ℕ} (hM : N = p * M) (hMpos : 0 < M) : addOrderOf (((M : ZMod N), (0 : ZMod N)) : V N) = p := by
  rw [Prod.addOrderOf_mk, addOrderOf_zero, Nat.lcm_one_right, ZMod.addOrderOf_coe M (NeZero.ne N)]
  conv_lhs => rw [hM]
  rw [Nat.gcd_mul_left_left, Nat.mul_div_cancel _ hMpos]

theorem natCard_fixedBy_S : Nat.card (fixedBy (X N) ModularGroup.S) = ModularCurve.nuTwo N := by
  rw [Nat.card_congr (fixedEquiv N ModularGroup.S (τS N) (lineOf_S_mul N))]
  refine ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuTwo N (τS N) (fun v => ?_) ?_
  · obtain ⟨x, y⟩ := v
    show ((-x : ZMod N), -y) = (-x, -y)
    rfl
  · intro p hp hpN
    obtain ⟨M, hM⟩ := hpN
    have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne N (by simpa using hM))
    refine ⟨((M : ZMod N), 0), addOrderOf_test N hM hMpos, fun k hk => ?_⟩
    have := congrArg Prod.snd hk
    simp [τS] at this
    exact natCast_M_ne_zero N hp hM hMpos this

theorem map_neg_eq (τ : V N →+ V N) (L : AddSubgroup (V N)) : L.map (-τ) = L.map τ := by
  ext w
  simp only [AddSubgroup.mem_map, AddMonoidHom.neg_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, L.neg_mem hv, by rw [map_neg]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨-v, L.neg_mem hv, by rw [map_neg, neg_neg]⟩

theorem natCard_fixedBy_ST :
    Nat.card (fixedBy (X N) (ModularGroup.S * ModularGroup.T)) = ModularCurve.nuThree N := by
  rw [Nat.card_congr (fixedEquiv N (ModularGroup.S * ModularGroup.T) (τST N) (lineOf_ST_mul N))]
  have e : {L : AddSubgroup (V N) // IsAddCyclic L ∧ Nat.card L = N ∧ L.map (τST N) = L}
      ≃ {L : AddSubgroup (V N) // IsAddCyclic L ∧ Nat.card L = N ∧ L.map (-τST N) = L} :=
    Equiv.subtypeEquivRight fun L => by rw [map_neg_eq]
  rw [Nat.card_congr e]
  refine ZMod.natCard_isAddCyclic_addSubgroup_prod_map_eq_nuThree N (-τST N) (fun v => ?_) ?_
  · obtain ⟨x, y⟩ := v
    ext <;> simp [τST] <;> try ring
  · intro p hp hpN
    obtain ⟨M, hM⟩ := hpN
    have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne N (by simpa using hM))
    refine ⟨((M : ZMod N), 0), addOrderOf_test N hM hMpos, fun k hk => ?_⟩
    have := congrArg Prod.snd hk
    simp [τST] at this
    exact natCast_M_ne_zero N hp hM hMpos this

end EllipticCount

theorem solution (N : ℕ) [NeZero N] :
    2 * Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
        (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ CongruenceSubgroup.Gamma0 N))
      = ModularCurve.dedekindPsi N + ModularCurve.nuTwo N := by
  rw [EllipticCount.two_mul_card_orbits_S N, EllipticCount.natCard_X, EllipticCount.natCard_fixedBy_S]

#print axioms solution

end
end S_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq
end P2MW
export P2MW.S_ModularCurve_two_mul_card_orbitRelQuotient_zpowers_S_gamma0_eq (solution)
