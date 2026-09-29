-- Prove2me | solution 1 for M4aLocalCFT.unitsDecomp_cohTrivial_of_inertia_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/813c17b2-1b30-5669-88a2-ac47d892cfd5

import Mathlib
import Definitions.Def_M4aLocalCFT_VocabDefs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot

set_option autoImplicit false

open IsLocalRing Finset

namespace M4aLocalCFT
p2m_export "M4aLocalCFT" "unitsAct unitsNorm unitsDerive"
p2m_open "M4aLocalCFT"

namespace UnramUnitsCoh

section Generic

variable {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]

def tr (g : G) (n : ℕ) (x : R) : R := ∑ j ∈ range n, g ^ j • x

def nm (g : G) (n : ℕ) (x : R) : R := ∏ j ∈ range n, g ^ j • x

def pn (g : G) (u : R) (j : ℕ) : R := ∏ i ∈ range j, g ^ i • u

def rs (g : G) (n : ℕ) (u lam : R) : R := ∑ j ∈ range n, pn g u j * g ^ j • lam

variable (R) in

def UnitComb (g : G) (n : ℕ) : Prop :=
  ∀ c : ℕ → R, (∃ j < n, IsUnit (c j)) → ∃ mu : R, IsUnit (∑ j ∈ range n, c j * g ^ j • mu)

theorem pow_smul_of_smul_eq {g : G} {c : R} (hc : g • c = c) (j : ℕ) : g ^ j • c = c := by
  induction j with
  | zero => rw [pow_zero, one_smul]
  | succ j ih => rw [pow_succ, mul_smul, hc, ih]

omit [MulSemiringAction G R] in
theorem sum_shift {g : G} {n : ℕ} (hn : g ^ n = 1) (F : G → R) :
    ∑ j ∈ range n, F (g ^ (j + 1)) = ∑ j ∈ range n, F (g ^ j) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => F (g ^ j)), hn, pow_zero]

omit [MulSemiringAction G R] in
theorem prod_shift {g : G} {n : ℕ} (hn : g ^ n = 1) (F : G → R) :
    ∏ j ∈ range n, F (g ^ (j + 1)) = ∏ j ∈ range n, F (g ^ j) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j => F (g ^ j)), hn, pow_zero]

theorem smul_tr {g : G} {n : ℕ} (hn : g ^ n = 1) (x : R) : g • tr g n x = tr g n x := by
  unfold tr
  rw [Finset.smul_sum]
  simp_rw [smul_smul, ← pow_succ']
  exact sum_shift hn (fun s => s • x)

theorem smul_nm {g : G} {n : ℕ} (hn : g ^ n = 1) (x : R) : g • nm g n x = nm g n x := by
  unfold nm
  rw [Finset.smul_prod']
  simp_rw [smul_smul, ← pow_succ']
  exact prod_shift hn (fun s => s • x)

theorem tr_mul_left {g : G} (n : ℕ) {c : R} (hc : g • c = c) (x : R) :
    tr g n (c * x) = c * tr g n x := by
  unfold tr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul', pow_smul_of_smul_eq hc]

theorem nm_mul (g : G) (n : ℕ) (x y : R) : nm g n (x * y) = nm g n x * nm g n y := by
  unfold nm
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => smul_mul' _ _ _

theorem isUnit_nm (g : G) (n : ℕ) {x : R} (hx : IsUnit x) : IsUnit (nm g n x) := by
  unfold nm
  exact IsUnit.prod_iff.mpr fun j _ => hx.map (MulSemiringAction.toRingHom G R (g ^ j))

theorem pn_zero (g : G) (u : R) : pn g u 0 = 1 := by simp [pn]

theorem pn_succ (g : G) (u : R) (j : ℕ) : pn g u (j + 1) = u * g • pn g u j := by
  unfold pn
  rw [Finset.prod_range_succ', pow_zero, one_smul, Finset.smul_prod', mul_comm]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [smul_smul, ← pow_succ']

theorem pn_eq_nm (g : G) (n : ℕ) (u : R) : pn g u n = nm g n u := rfl

theorem key_identity {g : G} {n : ℕ} (hn : g ^ n = 1) {u : R} (hu : nm g n u = 1) (lam : R) :
    u * g • rs g n u lam = rs g n u lam := by
  unfold rs
  rw [Finset.smul_sum, Finset.mul_sum]
  have h1 : ∀ j, u * g • (pn g u j * g ^ j • lam) = pn g u (j + 1) * g ^ (j + 1) • lam := by
    intro j
    rw [smul_mul', pn_succ, smul_smul, ← pow_succ', mul_assoc]
  simp_rw [h1]
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ' (fun j => pn g u j * g ^ j • lam), hn,
      pow_zero, one_smul, pn_zero, one_mul, pn_eq_nm, hu, one_mul]

theorem prod_one_add_mul (x : R) {ι : Type*} (s : Finset ι) (c : ι → R) :
    ∃ d : R, ∏ i ∈ s, (1 + x * c i) = 1 + x * ∑ i ∈ s, c i + x ^ 2 * d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨c a * ∑ i ∈ s, c i + d + x * c a * d, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, hd]
    ring

theorem exists_mul_smul_eq_of_nm_eq_one {g : G} {n : ℕ} (hD : UnitComb R g n)
    (hn : g ^ n = 1) (hpos : 0 < n) {u : R} (hu : nm g n u = 1) :
    ∃ y : R, IsUnit y ∧ u * g • y = y := by
  obtain ⟨mu, hmu⟩ := hD (pn g u) ⟨0, hpos, by rw [pn_zero]; exact isUnit_one⟩
  exact ⟨rs g n u mu, hmu, key_identity hn hu mu⟩

theorem exists_tr_eq {g : G} {n : ℕ} (hD : UnitComb R g n) (hn : g ^ n = 1) (hpos : 0 < n)
    {b : R} (hb : g • b = b) : ∃ z : R, tr g n z = b := by
  obtain ⟨mu, hmu⟩ := hD (fun _ => (1 : R)) ⟨0, hpos, isUnit_one⟩
  simp only [one_mul] at hmu
  have htfix : g • tr g n mu = tr g n mu := smul_tr hn mu
  obtain ⟨tU, htU⟩ := hmu
  change (tU : R) = tr g n mu at htU
  have htinvfix : g • ((tU⁻¹ : Rˣ) : R) = ((tU⁻¹ : Rˣ) : R) := by
    have h1 : g • ((tU⁻¹ : Rˣ) : R) * tr g n mu = 1 := by
      conv_lhs => rw [← htfix, ← smul_mul', ← htU, Units.inv_mul, smul_one]
    calc g • ((tU⁻¹ : Rˣ) : R)
        = g • ((tU⁻¹ : Rˣ) : R) * tr g n mu * ((tU⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, ← htU, Units.mul_inv, mul_one]
      _ = ((tU⁻¹ : Rˣ) : R) := by rw [h1, one_mul]
  refine ⟨b * ((tU⁻¹ : Rˣ) : R) * mu, ?_⟩
  have hcfix : g • (b * ((tU⁻¹ : Rˣ) : R)) = b * ((tU⁻¹ : Rˣ) : R) := by
    rw [smul_mul', hb, htinvfix]
  rw [tr_mul_left _ hcfix, mul_assoc, ← htU, Units.inv_mul, mul_one]

section Map

variable {S : Type*} [CommRing S] [MulSemiringAction G S]

theorem map_nm (f : R →+* S) (hf : ∀ (s : G) (x : R), f (s • x) = s • f x) (g : G) (n : ℕ)
    (x : R) : f (nm g n x) = nm g n (f x) := by
  unfold nm; rw [map_prod]; exact Finset.prod_congr rfl fun j _ => hf _ _

end Map

theorem prod_univ_eq_prod_range {M : Type*} [CommMonoid M] [Fintype G] {g : G}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (F : G → M) :
    ∏ s, F s = ∏ j ∈ range (orderOf g), F (g ^ j) := by
  have hord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  have hbij : Function.Bijective (fun j : Fin (orderOf g) => g ^ (j : ℕ)) := by
    rw [Fintype.bijective_iff_injective_and_card, Fintype.card_fin]
    exact ⟨fun i j hij => Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 hij), hord⟩
  rw [Finset.prod_range]
  exact (Fintype.prod_bijective _ hbij (fun j => F (g ^ (j : ℕ))) F (fun _ => rfl)).symm

end Generic

section Dedekind

variable {G k : Type*} [Group G] [Field k] [MulSemiringAction G k]

theorem dedekind (hinj : Function.Injective (MulSemiringAction.toRingAut G k)) (g : G)
    (c : ℕ → k) (hc : ∃ j < orderOf g, c j ≠ 0) :
    ∃ lam : k, ∑ j ∈ range (orderOf g), c j * g ^ j • lam ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j₀, hj₀, hc₀⟩ := hc
  apply hc₀
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin (orderOf g) → (k →* k), ∀ (j : Fin (orderOf g)) (x : k),
      χ j x = g ^ (j : ℕ) • x :=
    ⟨fun j => (MulSemiringAction.toRingHom G k (g ^ (j : ℕ))).toMonoidHom, fun _ _ => rfl⟩
  have hχinj : Function.Injective χ := by
    intro i j hij
    have h1 : g ^ (i : ℕ) = g ^ (j : ℕ) := by
      apply hinj
      apply RingEquiv.ext
      intro x
      change g ^ (i : ℕ) • x = g ^ (j : ℕ) • x
      rw [← hχ, ← hχ, hij]
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 h1)
  have hli := (linearIndependent_monoidHom k k).comp χ hχinj
  rw [Fintype.linearIndependent_iff] at hli
  have key := hli (fun i => c i) ?_ ⟨j₀, hj₀⟩
  · exact key
  · funext x
    have hx := h x
    rw [← Fin.sum_univ_eq_sum_range (fun j => c j * g ^ j • x)] at hx
    rw [Finset.sum_apply]
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hχ]
    exact hx

theorem unitComb_of_field (hinj : Function.Injective (MulSemiringAction.toRingAut G k))
    (g : G) : UnitComb k g (orderOf g) := by
  intro c hc
  obtain ⟨j, hj, hcj⟩ := hc
  obtain ⟨lam, hlam⟩ := dedekind hinj g c ⟨j, hj, hcj.ne_zero⟩
  exact ⟨lam, isUnit_iff_ne_zero.mpr hlam⟩

end Dedekind

section LocalLift

variable {G R : Type*} [Group G] [CommRing R] [IsLocalRing R] [MulSemiringAction G R]

theorem residue_smul' (s : G) (x : R) : residue R (s • x) = s • residue R x := rfl

theorem unitComb_of_residue
    (hinj : Function.Injective (MulSemiringAction.toRingAut G (ResidueField R))) (g : G) :
    UnitComb R g (orderOf g) := by
  intro c hc
  obtain ⟨j₀, hj₀, hc₀⟩ := hc
  obtain ⟨lam, hlam⟩ := dedekind hinj g (fun j => residue R (c j))
    ⟨j₀, hj₀, (residue_ne_zero_iff_isUnit _).mpr hc₀⟩
  obtain ⟨mu, rfl⟩ := residue_surjective lam
  refine ⟨mu, (residue_ne_zero_iff_isUnit _).mp ?_⟩
  have : residue R (∑ j ∈ range (orderOf g), c j * g ^ j • mu)
      = ∑ j ∈ range (orderOf g), residue R (c j) * g ^ j • residue R mu := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, residue_smul']
  rw [this]
  exact hlam

end LocalLift

section FiniteField

variable {G k : Type*} [Group G] [Field k] [MulSemiringAction G k]

noncomputable def uact (s : G) : kˣ →* kˣ :=
  Units.map (MulSemiringAction.toRingHom G k s).toMonoidHom

@[scoped simp] theorem coe_uact (s : G) (x : kˣ) : ((uact s x : kˣ) : k) = s • (x : k) := rfl

theorem exists_nm_eq_of_finite [Finite k] {g : G} {n : ℕ} (hD : UnitComb k g n)
    (hn : g ^ n = 1) (hpos : 0 < n) {a : k} (ha : a ≠ 0) (hfix : g • a = a) :
    ∃ x : k, x ≠ 0 ∧ nm g n x = a := by

  set Nk : kˣ →* kˣ := ∏ j ∈ range n, uact (g ^ j) with hNkdef
  set Dk : kˣ →* kˣ := uact g / MonoidHom.id kˣ with hDkdef
  have hNk : ∀ x : kˣ, ((Nk x : kˣ) : k) = nm g n (x : k) := by
    intro x
    rw [hNkdef, MonoidHom.finsetProd_apply, Units.coe_prod]
    rfl
  have hDk : ∀ x : kˣ, ((Dk x : kˣ) : k) = g • (x : k) * ((x : k))⁻¹ := by
    intro x
    rw [hDkdef, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul,
      coe_uact, Units.val_inv_eq_inv_val]

  have h1 : Nk.ker ≤ Dk.range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : nm g n (x : k) = 1 := by rw [← hNk, hx, Units.val_one]
    obtain ⟨y, hyU, hy⟩ := exists_mul_smul_eq_of_nm_eq_one hD hn hpos hx'
    have hy0 : y ≠ 0 := hyU.ne_zero
    have hgy0 : g • y ≠ 0 := fun h => hy0 ((smul_eq_zero_iff_eq g).mp h)
    refine ⟨(Units.mk0 y hy0)⁻¹, Units.ext ?_⟩
    rw [hDk, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, smul_inv'']
    rw [inv_mul_eq_iff_eq_mul₀ hgy0, mul_comm]
    exact hy.symm

  have h2 : Nk.range ≤ Dk.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hDk, hNk, Units.val_one, smul_nm hn, mul_inv_cancel₀]
    rw [← hNk]
    exact (Nk x).ne_zero

  have hcard : Nat.card Dk.ker ≤ Nat.card Nk.range := by
    have e1 := Subgroup.card_mul_index Dk.ker
    have e2 := Subgroup.card_mul_index Nk.ker
    rw [Subgroup.index_ker] at e1 e2
    have h3 : Nat.card Nk.ker ≤ Nat.card Dk.range := Subgroup.card_le_of_le h1
    have hpos' : 0 < Nat.card Dk.range := Nat.card_pos
    have : Nat.card Dk.ker * Nat.card Dk.range ≤ Nat.card Nk.range * Nat.card Dk.range :=
      calc Nat.card Dk.ker * Nat.card Dk.range
          = Nat.card Nk.ker * Nat.card Nk.range := by rw [e1, e2]
        _ ≤ Nat.card Dk.range * Nat.card Nk.range := Nat.mul_le_mul_right _ h3
        _ = Nat.card Nk.range * Nat.card Dk.range := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this hpos'
  have heq : Nk.range = Dk.ker := Subgroup.eq_of_le_of_card_ge h2 hcard

  have haU : Units.mk0 a ha ∈ Dk.ker := by
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [hDk, Units.val_mk0, hfix, mul_inv_cancel₀ ha, Units.val_one]
  rw [← heq] at haU
  obtain ⟨x, hx⟩ := haU
  refine ⟨x, x.ne_zero, ?_⟩
  rw [← hNk, hx, Units.val_mk0]

end FiniteField

section CompleteDVR

variable {G A : Type*} [Group G] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [MulSemiringAction G A]

theorem mem_maximalIdeal_pow_iff {ϖ : A} (hϖ : Irreducible ϖ) (m : ℕ) (x : A) :
    x ∈ maximalIdeal A ^ m ↔ ∃ a, x = ϖ ^ m * a := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [← ha, mul_comm]⟩
  · rintro ⟨a, ha⟩; exact ⟨a, by rw [ha, mul_comm]⟩

theorem smul_mem_maximalIdeal_pow {ϖ : A} (hϖ : Irreducible ϖ) {s : G} (hs : s • ϖ = ϖ)
    (m : ℕ) {x : A} (hx : x ∈ maximalIdeal A ^ m) : s • x ∈ maximalIdeal A ^ m := by
  rw [mem_maximalIdeal_pow_iff hϖ] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨s • a, by rw [smul_mul', smul_pow', hs]⟩

theorem nm_sub_nm_mem {ϖ : A} (hϖ : Irreducible ϖ) {g : G} (hg : g • ϖ = ϖ) (n m : ℕ)
    {x y : A} (h : x - y ∈ maximalIdeal A ^ m) :
    nm g n x - nm g n y ∈ maximalIdeal A ^ m := by
  rw [← Ideal.Quotient.eq] at h ⊢
  unfold nm
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.Quotient.eq, ← smul_sub]
  exact smul_mem_maximalIdeal_pow hϖ (pow_smul_of_smul_eq hg j) m ((Ideal.Quotient.eq).mp h)

theorem exists_fixed_uniformizer {g : G} {n : ℕ} (hD : UnitComb A g n) (hn : g ^ n = 1)
    (hpos : 0 < n) : ∃ ϖ : A, Irreducible ϖ ∧ g • ϖ = ϖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hc : ∀ j : ℕ, ∃ e : A, IsUnit e ∧ g ^ j • π = π * e := by
    intro j
    have hirr : Irreducible (g ^ j • π) :=
      (MulEquiv.irreducible_iff (MulSemiringAction.toRingEquiv G A (g ^ j))).mpr hπ
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_of_irreducible A hπ hirr
    exact ⟨e, e.isUnit, he.symm⟩
  choose c hcU hce using hc
  obtain ⟨mu, hmu⟩ := hD c ⟨0, hpos, hcU 0⟩
  refine ⟨π * ∑ j ∈ range n, c j * g ^ j • mu, (irreducible_mul_isUnit hmu).mpr hπ, ?_⟩
  have : π * ∑ j ∈ range n, c j * g ^ j • mu = tr g n (π * mu) := by
    unfold tr
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul', hce j, mul_assoc]
  rw [this]
  exact smul_tr hn _

theorem level_zero [Finite (ResidueField A)] {g : G} {n : ℕ}
    (hDk : UnitComb (ResidueField A) g n) (hn : g ^ n = 1) (hpos : 0 < n)
    (u : A) (huU : IsUnit u) (hu : g • u = u) :
    ∃ v : A, IsUnit v ∧ u - nm g n v ∈ maximalIdeal A := by
  have ha : residue A u ≠ 0 := (residue_ne_zero_iff_isUnit u).mpr huU
  have hafix : g • residue A u = residue A u := by rw [← residue_smul', hu]
  obtain ⟨x, hx0, hx⟩ := exists_nm_eq_of_finite hDk hn hpos ha hafix
  obtain ⟨v, rfl⟩ := residue_surjective x
  refine ⟨v, (residue_ne_zero_iff_isUnit v).mp hx0, ?_⟩
  rw [← residue_eq_zero_iff, map_sub, map_nm (residue A) residue_smul', hx, sub_self]

theorem level_step {g : G} {n : ℕ} (hD : UnitComb A g n) (hn : g ^ n = 1) (hpos : 0 < n)
    {ϖ : A} (hϖ : Irreducible ϖ) (hϖfix : g • ϖ = ϖ) {u : A} (hu : g • u = u) (m : ℕ)
    (v : A) (hvU : IsUnit v) (hv : ∃ b, u = nm g n v * (1 + ϖ ^ (m + 1) * b)) :
    ∃ v' : A, IsUnit v' ∧ (∃ b', u = nm g n v' * (1 + ϖ ^ (m + 2) * b')) ∧
      v' - v ∈ maximalIdeal A ^ (m + 1) := by
  obtain ⟨b, hb⟩ := hv
  have hmaxϖ : ϖ ∈ maximalIdeal A := hϖ.not_isUnit
  have hNvU : IsUnit (nm g n v) := isUnit_nm g n hvU
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero

  have hbfix : g • b = b := by
    have h0 : g • u = g • (nm g n v * (1 + ϖ ^ (m + 1) * b)) := by rw [← hb]
    rw [hu, smul_mul', smul_nm hn, smul_add, smul_one, smul_mul', smul_pow', hϖfix, hb] at h0
    have h2 := mul_left_cancel₀ hNvU.ne_zero h0
    have h3 := add_left_cancel h2
    exact (mul_left_cancel₀ (pow_ne_zero _ hϖ0) h3).symm
  obtain ⟨z, hz⟩ := exists_tr_eq hD hn hpos hbfix
  obtain ⟨d, hd⟩ := prod_one_add_mul (ϖ ^ (m + 1)) (range n) (fun j => g ^ j • z)
  have hnm1 : nm g n (1 + ϖ ^ (m + 1) * z)
      = 1 + ϖ ^ (m + 1) * b + (ϖ ^ (m + 1)) ^ 2 * d := by
    rw [← hz]
    unfold nm tr
    rw [← hd]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_add, smul_one, smul_mul', smul_pow', pow_smul_of_smul_eq hϖfix]
  have h1U : IsUnit (1 + ϖ ^ (m + 1) * z) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hmem : ϖ ^ (m + 1) * z ∈ maximalIdeal A :=
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hmaxϖ _ (Nat.succ_pos m))
    rw [map_add, map_one, (residue_eq_zero_iff _).mpr hmem, add_zero]
    exact one_ne_zero
  have hv'U : IsUnit (v * (1 + ϖ ^ (m + 1) * z)) := hvU.mul h1U
  obtain ⟨w, hw⟩ := isUnit_nm g n hv'U
  refine ⟨v * (1 + ϖ ^ (m + 1) * z), hv'U, ⟨-(ϖ ^ m * ↑w⁻¹ * nm g n v * d), ?_⟩, ?_⟩
  · have e1 : nm g n (v * (1 + ϖ ^ (m + 1) * z))
        = nm g n v * (1 + ϖ ^ (m + 1) * b + (ϖ ^ (m + 1)) ^ 2 * d) := by
      rw [nm_mul, hnm1]
    have hww : (w : A) * ↑w⁻¹ = 1 := Units.mul_inv w
    calc u = nm g n v * (1 + ϖ ^ (m + 1) * b) := hb
      _ = nm g n (v * (1 + ϖ ^ (m + 1) * z)) - nm g n v * (ϖ ^ (m + 1)) ^ 2 * d := by
          rw [e1]; ring
      _ = nm g n (v * (1 + ϖ ^ (m + 1) * z))
            * (1 + ϖ ^ (m + 2) * -(ϖ ^ m * ↑w⁻¹ * nm g n v * d)) := by
          rw [← hw]
          linear_combination (ϖ ^ m * ϖ ^ (m + 2) * nm g n v * d) * hww
  · have : v * (1 + ϖ ^ (m + 1) * z) - v = ϖ ^ (m + 1) * (v * z) := by ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmaxϖ _)

omit [IsDomain A] [IsDiscreteValuationRing A] in
theorem smodEq_pow_top_iff (I : Ideal A) (m : ℕ) (x y : A) :
    x ≡ y [SMOD (I ^ m • ⊤ : Submodule A A)] ↔ x - y ∈ I ^ m := by
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]

theorem exists_isUnit_nm_eq [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    {g : G} {n : ℕ} (hD : UnitComb A g n) (hDk : UnitComb (ResidueField A) g n)
    (hn : g ^ n = 1) (hpos : 0 < n) (u : A) (huU : IsUnit u) (hu : g • u = u) :
    ∃ v : A, IsUnit v ∧ nm g n v = u := by
  obtain ⟨ϖ, hϖ, hϖfix⟩ := exists_fixed_uniformizer hD hn hpos
  have hmaxϖ : ϖ ∈ maximalIdeal A := hϖ.not_isUnit

  let S : ℕ → Type _ := fun m => {v : A // IsUnit v ∧ ∃ b, u = nm g n v * (1 + ϖ ^ (m + 1) * b)}

  obtain ⟨v₀, hv₀U, hv₀⟩ := level_zero hDk hn hpos u huU hu
  have base : S 0 := by
    refine ⟨v₀, hv₀U, ?_⟩
    obtain ⟨w, hw⟩ := isUnit_nm g n hv₀U
    have hmem : u - nm g n v₀ ∈ maximalIdeal A ^ 1 := by rwa [pow_one]
    obtain ⟨a, ha⟩ := (mem_maximalIdeal_pow_iff hϖ 1 _).mp hmem
    refine ⟨a * ↑w⁻¹, ?_⟩
    rw [← hw] at ha ⊢
    have hww : (w : A) * ↑w⁻¹ = 1 := Units.mul_inv w
    linear_combination ha + (-(ϖ ^ 1 * a)) * hww

  have step : ∀ m, ∀ s : S m, ∃ s' : S (m + 1), s'.1 - s.1 ∈ maximalIdeal A ^ (m + 1) := by
    intro m s
    obtain ⟨v', hv'U, hv', hdiff⟩ := level_step hD hn hpos hϖ hϖfix hu m s.1 s.2.1 s.2.2
    exact ⟨⟨v', hv'U, hv'⟩, hdiff⟩
  choose next hnext using step
  let seq : ∀ m, S m := fun m => Nat.rec (motive := S) base (fun m s => next m s) m
  let f : ℕ → A := fun m => (seq m).1
  have hf_succ : ∀ m, f (m + 1) - f m ∈ maximalIdeal A ^ (m + 1) := fun m => hnext m (seq m)
  have hf_le : ∀ m j, f (m + j) - f m ∈ maximalIdeal A ^ (m + 1) := by
    intro m j
    induction j with
    | zero => rw [add_zero, sub_self]; exact Ideal.zero_mem _
    | succ j ih =>
      have h2 : f (m + j + 1) - f (m + j) ∈ maximalIdeal A ^ (m + 1) :=
        Ideal.pow_le_pow_right (by omega) (hf_succ (m + j))
      have := Ideal.add_mem _ h2 ih
      rwa [sub_add_sub_cancel] at this
  have hprec : ∀ {m j}, m ≤ j → f m ≡ f j [SMOD (maximalIdeal A ^ m • ⊤ : Submodule A A)] := by
    intro m j hmj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hmj
    rw [smodEq_pow_top_iff, ← neg_sub]
    exact (Ideal.neg_mem_iff _).mpr (Ideal.pow_le_pow_right (Nat.le_succ m) (hf_le m i))
  obtain ⟨Lv, hLv⟩ := IsPrecomplete.prec' (I := maximalIdeal A) f hprec
  have hLv' : ∀ m, f m - Lv ∈ maximalIdeal A ^ m := fun m =>
    (smodEq_pow_top_iff _ _ _ _).mp (hLv m)

  have hLvU : IsUnit Lv := by
    have h1 := hLv' 1
    rw [pow_one, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at h1
    have h2 : residue A (f 1) ≠ 0 := (residue_ne_zero_iff_isUnit _).mpr (seq 1).2.1
    rw [h1] at h2
    exact (residue_ne_zero_iff_isUnit _).mp h2
  refine ⟨Lv, hLvU, ?_⟩

  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := maximalIdeal A) (nm g n Lv - u)
  intro m
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  have e1 : nm g n Lv - nm g n (f m) ∈ maximalIdeal A ^ m := by
    apply nm_sub_nm_mem hϖ hϖfix
    rw [← neg_sub]
    exact (Ideal.neg_mem_iff _).mpr (hLv' m)
  have e2 : nm g n (f m) - u ∈ maximalIdeal A ^ m := by
    obtain ⟨b, hb⟩ := (seq m).2.2
    have hb' : u = nm g n (f m) * (1 + ϖ ^ (m + 1) * b) := hb
    have : nm g n (f m) - u = -(ϖ ^ (m + 1) * (nm g n (f m) * b)) := by
      linear_combination (-1 : A) * hb'
    rw [this]
    exact (Ideal.neg_mem_iff _).mpr (Ideal.pow_le_pow_right (Nat.le_succ m)
      (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmaxϖ _)))
  have := Ideal.add_mem _ e1 e2
  rwa [sub_add_sub_cancel] at this

end CompleteDVR

section Card

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (A : ValuationSubring L)

theorem coe_unitsAct (s : A.decompositionSubgroup K) (v : Aˣ) :
    ((unitsAct A s v : Aˣ) : A) = s • (v : A) := rfl

theorem coe_unitsNorm [Finite (A.decompositionSubgroup K)] {g : A.decompositionSubgroup K}
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (v : Aˣ) :
    ((unitsNorm (K := K) A v : Aˣ) : A) = nm g (orderOf g) (v : A) := by
  letI := Fintype.ofFinite (A.decompositionSubgroup K)
  show (((∏ s : A.decompositionSubgroup K, unitsAct A s) v : Aˣ) : A) = _
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, prod_univ_eq_prod_range hg]
  rfl

theorem unitsDerive_apply (g : A.decompositionSubgroup K) (v : Aˣ) :
    unitsDerive A g v = unitsAct A g v / v := rfl

theorem mem_ker_unitsDerive_iff (g : A.decompositionSubgroup K) (v : Aˣ) :
    v ∈ (unitsDerive A g).ker ↔ g • (v : A) = v := by
  rw [MonoidHom.mem_ker, unitsDerive_apply, div_eq_one, Units.ext_iff, coe_unitsAct]

variable [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
variable [Finite (IsLocalRing.ResidueField A)]
variable [Finite (A.decompositionSubgroup K)]

variable (K) in

theorem unitsDecomp_cohTrivial
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hur : A.inertiaSubgroup K = ⊥) :
    (unitsDerive A g).ker ≤ (unitsNorm (K := K) A).range ∧
    (unitsNorm (K := K) A).ker ≤ (unitsDerive A g).range := by
  have hn : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hpos : 0 < orderOf g := orderOf_pos g
  have hinj : Function.Injective
      (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hur
  have hD : UnitComb A g (orderOf g) := unitComb_of_residue hinj g
  have hDk : UnitComb (ResidueField A) g (orderOf g) := unitComb_of_field hinj g
  constructor
  ·
    intro u hu
    rw [mem_ker_unitsDerive_iff] at hu
    obtain ⟨v, hvU, hv⟩ := exists_isUnit_nm_eq hD hDk hn hpos (u : A) u.isUnit hu
    obtain ⟨vU, rfl⟩ := hvU
    exact ⟨vU, Units.ext (by rw [coe_unitsNorm A hg]; exact hv)⟩
  ·
    intro u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, coe_unitsNorm A hg, Units.val_one] at hu
    obtain ⟨y, hyU, hy⟩ := exists_mul_smul_eq_of_nm_eq_one hD hn hpos hu
    obtain ⟨yU, rfl⟩ := hyU
    refine ⟨yU⁻¹, Units.ext ?_⟩
    rw [unitsDerive_apply, div_eq_mul_inv, inv_inv, Units.val_mul, coe_unitsAct]
    calc g • ((yU⁻¹ : Aˣ) : A) * yU
        = g • ((yU⁻¹ : Aˣ) : A) * (u * g • (yU : A)) := by rw [hy]
      _ = u * (g • (((yU⁻¹ : Aˣ) : A) * yU)) := by rw [smul_mul']; ring
      _ = u := by rw [Units.inv_mul, smul_one, mul_one]

end Card

end UnramUnitsCoh
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot.M4aLocalCFT.UnramUnitsCoh"

end M4aLocalCFT
p2m_reactivate "P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot.M4aLocalCFT.UnramUnitsCoh P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot.M4aLocalCFT"

theorem solution (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal (A : Type _)) A]
    [Finite (IsLocalRing.ResidueField A)]
    [Finite (A.decompositionSubgroup K)] [IsCyclic (A.decompositionSubgroup K)]
    (g : A.decompositionSubgroup K) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hur : A.inertiaSubgroup K = ⊥) :
    (M4aLocalCFT.unitsDerive A g).ker ≤ (M4aLocalCFT.unitsNorm (K := K) A).range ∧
    (M4aLocalCFT.unitsNorm (K := K) A).ker ≤ (M4aLocalCFT.unitsDerive A g).range :=
  M4aLocalCFT.UnramUnitsCoh.unitsDecomp_cohTrivial K A g hg hur

end S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot
end P2MW
export P2MW.S_M4aLocalCFT_unitsDecomp_cohTrivial_of_inertia_eq_bot (solution)
