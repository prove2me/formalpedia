-- Prove2me | solution 1 for GlobalTheory.exists_induced_int_prime_to
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:39.952541+00:00
-- url     : https://prove2.me/submissions/8af075b5-44be-4794-a3e0-6d8dc7e683ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsInducedIntPrimeTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.ElemLocal
end GlobalTheory.ElemLocal
open Polynomial in
private theorem exists_commute_coprime_mul_prime_power_order {G : Type} [Group G] [Finite G] (x : G) {p : ℕ}
    (hp : p.Prime) : ∃ c q : G, x = c * q ∧ Commute c q ∧ Nat.Coprime p (orderOf c) ∧
      ∃ a : ℕ, q ^ p ^ a = 1 := by
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hcop : Nat.Coprime (p ^ (orderOf x).factorization p)
      (orderOf x / p ^ (orderOf x).factorization p) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  have hnm := Nat.ordProj_mul_ordCompl_eq_self (orderOf x) p
  set a := (orderOf x).factorization p
  set m := orderOf x / p ^ a
  have hb := Nat.gcd_eq_gcd_ab (p ^ a) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hx : ∀ k : ℤ, x ^ ((orderOf x : ℤ) * k) = 1 := fun k => by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨x ^ (((p ^ a : ℕ) : ℤ) * Nat.gcdA (p ^ a) m), x ^ ((m : ℤ) * Nat.gcdB (p ^ a) m),
    ?_, (Commute.refl x).zpow_zpow _ _, ?_, a, ?_⟩
  · rw [← zpow_add, ← hb, zpow_one]
  · have h1 : (x ^ (((p ^ a : ℕ) : ℤ) * Nat.gcdA (p ^ a) m)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      convert hx (Nat.gcdA (p ^ a) m) using 2
      rw [← hnm]; push_cast; ring
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h1)
      (Nat.coprime_ordCompl hp hn0)
  · rw [← zpow_natCast, ← zpow_mul]
    convert hx (Nat.gcdB (p ^ a) m) using 2
    rw [← hnm]; push_cast; ring
open Polynomial in
private theorem zpow_mul_zpow_eq_of_commute_of_zpow_eq {G : Type} [Group G] {c w : G} (hcw : Commute c w)
    {M : ℤ} (hc : c ^ M = c) (hw : w ^ M = 1) (i : ℤ) : (c ^ i * w) ^ M = c ^ i := by
  rw [(hcw.zpow_left i).mul_zpow, ← zpow_mul, mul_comm i M, zpow_mul, hc, hw, mul_one]
open Polynomial in
private theorem inv_mul_mul_zpow {G : Type} [Group G] (s a : G) (n : ℤ) :
    (s⁻¹ * a * s) ^ n = s⁻¹ * a ^ n * s := by
  have := map_zpow (MulAut.conj s⁻¹) a n
  simp only [MulAut.conj_apply, inv_inv] at this
  exact this.symm
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open Polynomial
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ (E : Subgroup G) (f : G → ℤ) (ι : Type) (_ : Fintype ι) (r : ι → ℂ) (lam : ι → E →* ℂˣ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ¬ (p : ℤ) ∣ f x ∧ (∀ i, IsIntegral ℤ (r i)) ∧ ∀ g, (f g : ℂ) = ∑ i, r i * _root_.GlobalTheory.BI.ind E (fun e => (lam i e : ℂ)) g := by
  intro G _ _ x p hp
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite G
  obtain ⟨c, q, rfl, hcq, hco, a, hqa⟩ := exists_commute_coprime_mul_prime_power_order x hp
  set Z : Subgroup G := Subgroup.centralizer {c} with hZ
  have memZ : ∀ s : G, s ∈ Z ↔ c * s = s * c := fun s => by
    simp only [hZ, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  have hqZ : q ∈ Z := (memZ q).mpr hcq.eq
  set qZ : Z := ⟨q, hqZ⟩ with hqZdef
  have hQ : IsPGroup p (Subgroup.zpowers qZ) := by
    rintro ⟨g, i, rfl⟩
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one, hqZdef]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqa, one_zpow]
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  set P' : Subgroup G := (P : Subgroup Z).map Z.subtype with hP'
  have hqP' : q ∈ P' := ⟨qZ, hQP (Subgroup.mem_zpowers qZ), rfl⟩
  have hPc : ∀ y ∈ P', Commute c y := by
    rintro _ ⟨z, -, rfl⟩
    exact (memZ z).mp z.2
  set E := _root_.GlobalTheory.ElemLocal.cycMul c P' hPc with hE
  have hcE : c ∈ E := ⟨1, 1, P'.one_mem, by simp⟩
  have hP'E : P' ≤ E := fun y hy => ⟨0, y, hy, by simp⟩
  set o := orderOf c with hodef
  set N := Nat.card (P : Subgroup Z) with hNdef
  have hNP' : Nat.card P' = N := Subgroup.card_subtype Z P
  obtain ⟨k, hk⟩ := P.2.exists_card_eq
  have hNo : Nat.Coprime N o := by rw [hNdef, hk]; exact Nat.Coprime.pow_left k hco
  have hb := Nat.gcd_eq_gcd_ab N o
  rw [hNo.gcd_eq_one, Nat.cast_one] at hb
  set M : ℤ := (N : ℤ) * Nat.gcdA N o with hM
  have hcM : c ^ M = c := by
    have h1 : c ^ ((o : ℤ) * Nat.gcdB N o) = 1 := by
      rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    calc c ^ M = c ^ M * c ^ ((o : ℤ) * Nat.gcdB N o) := by rw [h1, mul_one]
      _ = c := by rw [← zpow_add, hM, ← hb, zpow_one]
  have hwM : ∀ w ∈ P', w ^ M = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : (⟨z, hz⟩ : (P : Subgroup Z)) ^ N = 1 := pow_card_eq_one'
    have h2 : (z : G) ^ N = 1 := by
      have := congrArg (fun u : (P : Subgroup Z) => ((u : Z) : G)) h1
      simpa using this
    show (z : G) ^ M = 1
    rw [hM, zpow_mul, zpow_natCast, h2, one_zpow]
  have hpowE : ∀ i : ℤ, ∀ y ∈ P', (c ^ i * y) ^ M = c ^ i := fun i y hy =>
    zpow_mul_zpow_eq_of_commute_of_zpow_eq (hPc y hy) hcM (hwM y hy) i
  have hmul : ∀ e₁ ∈ E, ∀ e₂ ∈ E, (e₁ * e₂) ^ M = e₁ ^ M * e₂ ^ M := by
    rintro _ ⟨i, y, hy, rfl⟩ _ ⟨j, z, hz, rfl⟩
    have h : c ^ i * y * (c ^ j * z) = c ^ (i + j) * (y * z) := by
      rw [zpow_add, mul_assoc, ← mul_assoc y, ← ((hPc y hy).zpow_left j).eq]
      simp only [mul_assoc]
    rw [h, hpowE _ _ (P'.mul_mem hy hz), hpowE _ _ hy, hpowE _ _ hz, zpow_add]
  have hker : ∀ e ∈ E, e ^ M = 1 → e ∈ P' := by
    rintro _ ⟨i, y, hy, rfl⟩ h
    rw [hpowE _ _ hy] at h
    rwa [h, one_mul]
  have hcent : ∀ t : E, (∃ n : ℤ, (t : G) = c ^ n) → t ∈ Subgroup.center E := by
    rintro t ⟨n, hn⟩
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, i, y, hy, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hn]
    exact ((Commute.zpow_zpow_self c i n).mul_left ((hPc y hy).zpow_left n).symm).eq
  have hl : ∀ y : E, ∃ j : ℕ, y ^ p ^ j ∈ Subgroup.center E := by
    rintro ⟨_, i, _, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := P.2 ⟨z, hz⟩
    refine ⟨j, hcent _ ⟨i * ((p ^ j : ℕ) : ℤ), ?_⟩⟩
    have h2 : (z : G) ^ p ^ j = 1 := by
      have := congrArg (fun u : (P : Subgroup Z) => ((u : Z) : G)) hj
      simpa using this
    simp only [SubgroupClass.coe_pow, Subgroup.coe_subtype]
    rw [((hPc (z : G) ⟨z, hz, rfl⟩).zpow_left i).mul_pow, h2, mul_one, ← zpow_natCast, ← zpow_mul]
  have ho : o ≠ 0 := (orderOf_pos c).ne'
  have hζ := Complex.isPrimitiveRoot_exp o ho
  set ζ : ℂˣ := Units.mk0 _ (hζ.ne_zero ho) with hζdef
  have hζu : IsPrimitiveRoot ζ o := IsPrimitiveRoot.coe_units_iff.mp hζ
  set cE : E := ⟨c, hcE⟩ with hcEdef
  have hord : orderOf cE = orderOf ζ := by
    rw [← Subgroup.orderOf_coe cE, ← hζu.eq_orderOf]
  have hφmem : ∀ e : E, e ^ M ∈ Subgroup.zpowers cE := by
    rintro ⟨_, i, y, hy, rfl⟩
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_zpow, hcEdef]
    rw [hpowE _ _ hy]
  let φ : E →* Subgroup.zpowers cE :=
    { toFun := fun e => ⟨e ^ M, hφmem e⟩
      map_one' := by ext; simp
      map_mul' := fun e₁ e₂ => by
        ext
        simpa using hmul e₁ e₁.2 e₂ e₂.2 }
  have hφ : ∀ e : E, ((φ e : E) : G) = (e : G) ^ M := fun e => by simp [φ]
  have hpowmem : ∀ e : E, (e : G) ^ M ∈ Subgroup.zpowers c := by
    rintro ⟨_, i, y, hy, rfl⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, (hpowE _ _ hy).symm⟩
  have hζiff : ∀ m n : ℤ, c ^ m = c ^ n ↔ ζ ^ m = ζ ^ n := fun m n => by
    rw [zpow_eq_zpow_iff_modEq, zpow_eq_zpow_iff_modEq, ← hζu.eq_orderOf]
  let d : E → ℤ := fun e => Classical.choose (Subgroup.mem_zpowers_iff.mp (hpowmem e))
  have hd : ∀ e : E, c ^ d e = (e : G) ^ M := fun e =>
    Classical.choose_spec (Subgroup.mem_zpowers_iff.mp (hpowmem e))
  let χ : E →* ℂˣ :=
    { toFun := fun e => ζ ^ d e
      map_one' := by
        rw [← zpow_zero ζ, ← hζiff, hd]; simp
      map_mul' := fun e₁ e₂ => by
        rw [← zpow_add, ← hζiff, zpow_add, hd, hd, hd]
        exact hmul _ e₁.2 _ e₂.2 }
  have hχ : ∀ e : E, χ e = ζ ↔ (e : G) ^ M = c := fun e => by
    show ζ ^ d e = ζ ↔ _
    rw [← hd e]
    have := hζiff (d e) 1
    simp only [zpow_one] at this
    exact this.symm
  have hχpow : ∀ e : E, (χ e) ^ o = 1 := fun e => by
    show (ζ ^ d e) ^ o = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζu.pow_eq_one, one_zpow]

  have hψ : ∀ e : E, ∑ k : Fin o, ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ) *
      ((((powMonoidHom (k : ℕ)).comp χ) e : ℂˣ) : ℂ) = if (e : G) ^ M = c then (o : ℂ) else 0 := by
    intro e
    have hsum : ∑ k : Fin o, ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ) *
        ((((powMonoidHom (k : ℕ)).comp χ) e : ℂˣ) : ℂ) =
        ∑ k ∈ Finset.range o, (((ζ⁻¹ * χ e : ℂˣ)) : ℂ) ^ k := by
      rw [Finset.sum_range (fun k => (((ζ⁻¹ * χ e : ℂˣ)) : ℂ) ^ k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_pow]
    rw [hsum]
    split_ifs with h
    · have : χ e = ζ := (hχ e).mpr h
      simp [this]
    · have hw1 : (((ζ⁻¹ * χ e : ℂˣ)) : ℂ) ≠ 1 := by
        intro h1
        apply h
        rw [← hχ e]
        have h2 : ζ⁻¹ * χ e = 1 := Units.ext h1
        rw [inv_mul_eq_one] at h2
        exact h2.symm
      have hwo : (((ζ⁻¹ * χ e : ℂˣ)) : ℂ) ^ o = 1 := by
        rw [← Units.val_pow_eq_pow_val, mul_pow, hχpow, inv_pow, hζu.pow_eq_one, inv_one,
          one_mul, Units.val_one]
      have := geom_sum_mul (((ζ⁻¹ * χ e : ℂˣ)) : ℂ) o
      rw [hwo, sub_self] at this
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hw1)
  have hcardE : Nat.card E = o * N := by
    have hsurj : Function.Surjective φ := by
      rintro ⟨_, n, rfl⟩
      refine ⟨cE ^ n, Subtype.ext (Subtype.ext ?_)⟩
      rw [hφ]
      simp only [SubgroupClass.coe_zpow, hcEdef]
      rw [← zpow_mul, mul_comm, zpow_mul, hcM]
    have hkerφ : φ.ker = P'.subgroupOf E := by
      ext e
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        apply hker _ e.2
        rw [← hφ, h]; rfl
      · intro h
        apply Subtype.ext; apply Subtype.ext
        rw [hφ]; exact hwM _ h
    calc Nat.card E = Nat.card φ.ker * φ.ker.index := φ.ker.card_mul_index.symm
      _ = N * o := by
        rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_zpowers,
          ← Subgroup.orderOf_coe cE, hkerφ,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'E).toEquiv, hNP']
      _ = o * N := Nat.mul_comm _ _
  have hinv : ∀ g s w : G, w ∈ P' → (s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c) →
      ((s * w)⁻¹ * g * (s * w) ∈ E ∧ ((s * w)⁻¹ * g * (s * w)) ^ M = c) := by
    rintro g s w hw ⟨h1, h2⟩
    have hre : (s * w)⁻¹ * g * (s * w) = w⁻¹ * (s⁻¹ * g * s) * w := by group
    rw [hre, inv_mul_mul_zpow, h2]
    refine ⟨E.mul_mem (E.mul_mem (E.inv_mem (hP'E hw)) h1) (hP'E hw), ?_⟩
    rw [mul_assoc, (hPc w hw).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdvd : ∀ g : G, N ∣ Nat.card {s : G // s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c} := by
    intro g
    set S : Set G := {s | s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c} with hSdef
    have hS : S = QuotientGroup.mk ⁻¹' (QuotientGroup.mk '' S : Set (G ⧸ P')) := by
      ext t
      constructor
      · intro ht; exact ⟨t, ht, rfl⟩
      · rintro ⟨s, hs, hst⟩
        have hw : s⁻¹ * t ∈ P' := QuotientGroup.eq.mp hst
        have := hinv g s _ hw hs
        rwa [mul_inv_cancel_left] at this
    have : Nat.card {s : G // s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c} = Nat.card S := rfl
    rw [this, hS, QuotientGroup.card_preimage_mk, hNP']
    exact dvd_mul_right _ _
  have hxM : (c * q) ^ M = c := by simpa using hpowE 1 q hqP'
  have hcond : ∀ s : G, (s⁻¹ * (c * q) * s ∈ E ∧ (s⁻¹ * (c * q) * s) ^ M = c) ↔
      (s ∈ Z ∧ s⁻¹ * q * s ∈ P') := by
    intro s
    rw [inv_mul_mul_zpow, hxM]
    have hZc : s ∈ Z ↔ s⁻¹ * c * s = c := by
      rw [memZ]
      constructor
      · intro h; rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      · intro h
        calc c * s = s * (s⁻¹ * c * s) := by group
          _ = s * c := by rw [h]
    rw [hZc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, hker _ ?_ ?_⟩
      · have : s⁻¹ * q * s = c⁻¹ * (s⁻¹ * (c * q) * s) := by
          calc s⁻¹ * q * s = (s⁻¹ * c * s)⁻¹ * (s⁻¹ * (c * q) * s) := by group
            _ = c⁻¹ * (s⁻¹ * (c * q) * s) := by rw [h2]
        rw [this]; exact E.mul_mem (E.inv_mem hcE) h1
      · rw [inv_mul_mul_zpow, hwM q hqP', mul_one, inv_mul_cancel]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      have : s⁻¹ * (c * q) * s = (s⁻¹ * c * s) * (s⁻¹ * q * s) := by group
      rw [this, h1]; exact E.mul_mem hcE (hP'E h2)
  have hfix : ∀ z : Z, ((z : Z ⧸ (P : Subgroup Z)) ∈
      MulAction.fixedPoints (Subgroup.zpowers qZ) (Z ⧸ (P : Subgroup Z)) ↔
      z⁻¹ * qZ * z ∈ (P : Subgroup Z)) := by
    intro z
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      have h1 : (qZ⁻¹ : Z) • (z : Z ⧸ (P : Subgroup Z)) = z :=
        h ⟨qZ⁻¹, Subgroup.inv_mem _ (Subgroup.mem_zpowers qZ)⟩
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at h1
      simpa [smul_eq_mul, mul_inv_rev, mul_assoc] using h1
    · rintro h ⟨_, i, rfl⟩
      show (qZ ^ i : Z) • (z : Z ⧸ (P : Subgroup Z)) = z
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
      have : (qZ ^ i * z)⁻¹ * z = (z⁻¹ * qZ * z) ^ (-i) := by
        rw [inv_mul_mul_zpow]; group
      rw [this]; exact Subgroup.zpow_mem _ h _
  have hP'Z : ∀ z : Z, ((z : G)⁻¹ * q * z ∈ P' ↔ z⁻¹ * qZ * z ∈ (P : Subgroup Z)) := fun z => by
    have h : Z.subtype (z⁻¹ * qZ * z) ∈ (P : Subgroup Z).map Z.subtype ↔
        z⁻¹ * qZ * z ∈ (P : Subgroup Z) := Subgroup.mem_map_iff_mem Z.subtype_injective
    exact h
  have hcardx : Nat.card {s : G // s⁻¹ * (c * q) * s ∈ E ∧ (s⁻¹ * (c * q) * s) ^ M = c} =
      N * Nat.card (MulAction.fixedPoints (Subgroup.zpowers qZ) (Z ⧸ (P : Subgroup Z))) := by
    have e1 : {s : G // s⁻¹ * (c * q) * s ∈ E ∧ (s⁻¹ * (c * q) * s) ^ M = c} ≃
        (QuotientGroup.mk ⁻¹' (MulAction.fixedPoints (Subgroup.zpowers qZ)
          (Z ⧸ (P : Subgroup Z))) : Set Z) :=
      { toFun := fun s => ⟨⟨s.1, ((hcond s.1).mp s.2).1⟩,
          (hfix _).mpr ((hP'Z ⟨s.1, ((hcond s.1).mp s.2).1⟩).mp ((hcond s.1).mp s.2).2)⟩
        invFun := fun z => ⟨z.1.1, (hcond z.1.1).mpr ⟨z.1.2, (hP'Z z.1).mpr ((hfix _).mp z.2)⟩⟩
        left_inv := fun s => rfl
        right_inv := fun z => rfl }
    rw [Nat.card_congr e1, QuotientGroup.card_preimage_mk]
  refine ⟨E, fun g => ((Nat.card {s : G // s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c} / N : ℕ) : ℤ),
    Fin o, inferInstance, fun k => ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ),
    fun k => (powMonoidHom (k : ℕ)).comp χ, ⟨p, hp, hl⟩, ?_, ?_, ?_⟩
  · show ¬ (p : ℤ) ∣ ((Nat.card {s : G // s⁻¹ * (c * q) * s ∈ E ∧
      (s⁻¹ * (c * q) * s) ^ M = c} / N : ℕ) : ℤ)
    rw [hcardx, Nat.mul_div_cancel_left _ Nat.card_pos, Int.natCast_dvd_natCast]
    intro hdiv
    have hmod := hQ.card_modEq_card_fixedPoints (Z ⧸ (P : Subgroup Z))
    exact P.not_dvd_index ((hmod.dvd_iff (dvd_refl p)).mpr hdiv)
  · intro k
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero ho) ?_
    have : ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ) ^ o = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, inv_pow, hζu.pow_eq_one,
        inv_one, one_pow, Units.val_one]
    rw [this]; exact isIntegral_one
  · intro g
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := (P : Subgroup Z))).ne'
    have ho0 : (o : ℂ) ≠ 0 := by exact_mod_cast ho
    have hR : ∑ k : Fin o, ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ) * _root_.GlobalTheory.BI.ind E
        (fun e => ((((powMonoidHom (k : ℕ)).comp χ) e : ℂˣ) : ℂ)) g =
        (Nat.card E : ℂ)⁻¹ * ∑ s : G,
          if s⁻¹ * g * s ∈ E ∧ (s⁻¹ * g * s) ^ M = c then (o : ℂ) else 0 := by
      simp only [_root_.GlobalTheory.BI.ind, finsum_eq_sum_of_fintype, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [_root_.GlobalTheory.BI.ext0]
      by_cases h : s⁻¹ * g * s ∈ E
      · simp only [dif_pos h, h, true_and]
        calc _ = (Nat.card E : ℂ)⁻¹ * ∑ k : Fin o, ((ζ⁻¹ ^ (k : ℕ) : ℂˣ) : ℂ) *
              ((((powMonoidHom (k : ℕ)).comp χ) ⟨_, h⟩ : ℂˣ) : ℂ) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _
          _ = _ := by rw [hψ] <;> rfl
      · simp [h]
    refine Eq.trans ?_ hR.symm
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcardE]
    rw [Int.cast_natCast, Nat.cast_div (hdvd g) hN0, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    push_cast
    field_simp
end _root_.GlobalTheory
