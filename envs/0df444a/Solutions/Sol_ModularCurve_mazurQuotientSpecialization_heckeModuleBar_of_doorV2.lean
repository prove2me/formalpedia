-- Prove2me | solution 1 for ModularCurve.mazurQuotientSpecialization_heckeModuleBar_of_doorV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/a2917c3a-2f86-5ee8-8691-b6ed26db7ba8

import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_mazurQuotientSpecialization_heckeModuleBar_of_doorV2

open ModularCurve AlgebraicCurve IsLocalRing

set_option autoImplicit false

noncomputable section

section AbstractHelpers

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

private theorem n3red_smul_int_comm (r : R) (n : ℤ) (x : M) : r • (n • x) = n • (r • x) :=
  smul_comm r n x

private theorem n3red_smul_nat_comm (r : R) (n : ℕ) (x : M) : r • (n • x) = n • (r • x) :=
  smul_comm r n x

variable (R M) in

private def n3redQTors (q : ℕ) : Submodule R M where
  carrier := {x | ∃ n : ℕ, q ^ n • x = 0}
  zero_mem' := ⟨0, smul_zero _⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨k, hk⟩
    refine ⟨n + k, ?_⟩
    have hx : q ^ (n + k) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hn, smul_zero]
    have hy : q ^ (n + k) • y = 0 := by rw [pow_add, mul_smul, hk, smul_zero]
    rw [smul_add, hx, hy, add_zero]
  smul_mem' := by
    rintro c x ⟨n, hn⟩
    exact ⟨n, by rw [← n3red_smul_nat_comm, hn, smul_zero]⟩

private theorem n3redQTors_mem {q : ℕ} {x : M} :
    x ∈ n3redQTors R M q ↔ ∃ n : ℕ, q ^ n • x = 0 := Iff.rfl

private theorem n3red_coprime_kill (a b : ℕ) (hcop : Nat.Coprime a b) {x : M}
    (ha : a • x = 0) (hb : b • x = 0) : x = 0 := by
  have hg := Nat.gcd_eq_gcd_ab a b
  have hcop' : Nat.gcd a b = 1 := hcop
  rw [hcop', Nat.cast_one] at hg
  have h1 : ((a : ℤ) * Nat.gcdA a b) • x = 0 := by
    rw [mul_comm, mul_smul, natCast_zsmul, ha, smul_zero]
  have h2 : ((b : ℤ) * Nat.gcdB a b) • x = 0 := by
    rw [mul_comm, mul_smul, natCast_zsmul, hb, smul_zero]
  have h3 : (1 : ℤ) • x = 0 := by rw [hg, add_smul, h1, h2, add_zero]
  rwa [one_zsmul] at h3

private theorem n3red_smulTop_div (I : Ideal R)
    (hdiv : ∀ m : ℤ, m ≠ 0 → ∀ x : M, ∃ y : M, m • y = x)
    (m : ℤ) (hm : m ≠ 0) {w : M} (hw : w ∈ I • (⊤ : Submodule R M)) :
    ∃ w' ∈ I • (⊤ : Submodule R M), m • w' = w := by
  refine Submodule.smul_induction_on hw (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨y, hy⟩ := hdiv m hm x
    exact ⟨a • y, Submodule.smul_mem_smul ha trivial, by rw [← n3red_smul_int_comm, hy]⟩
  · obtain ⟨x', hx', hxe⟩ := hx
    obtain ⟨y', hy', hye⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', by rw [smul_add, hxe, hye]⟩

private theorem n3red_torsion_lift (I : Ideal R)
    (hdiv : ∀ m : ℤ, m ≠ 0 → ∀ x : M, ∃ y : M, m • y = x)
    (m : ℕ) (hm : m ≠ 0) {x : M} (hx : m • x ∈ I • (⊤ : Submodule R M)) :
    ∃ u : M, m • u = 0 ∧ x - u ∈ I • (⊤ : Submodule R M) := by
  obtain ⟨w', hw', hmw'⟩ := n3red_smulTop_div I hdiv (m : ℤ) (Int.natCast_ne_zero.mpr hm) hx
  refine ⟨x - w', ?_, ?_⟩
  · have h1 : m • w' = m • x := by rw [← natCast_zsmul w' m, hmw']
    rw [smul_sub, h1, sub_self]
  · rw [sub_sub_cancel]
    exact hw'

private theorem n3red_bezout_split (q e m' : ℕ) (hcop : Nat.Coprime (q ^ e) m') (x : M)
    (hx : (q ^ e * m') • x = 0) :
    ∃ c₁ c₂ : ℤ, x = c₁ • x + c₂ • x ∧ q ^ e • (c₁ • x) = 0 ∧ m' • (c₂ • x) = 0 := by
  have hg := Nat.gcd_eq_gcd_ab (q ^ e) m'
  have hcop' : Nat.gcd (q ^ e) m' = 1 := hcop
  rw [hcop', Nat.cast_one] at hg
  refine ⟨(m' : ℤ) * Nat.gcdB (q ^ e) m', ((q ^ e : ℕ) : ℤ) * Nat.gcdA (q ^ e) m', ?_, ?_, ?_⟩
  · have hone : ((m' : ℤ) * Nat.gcdB (q ^ e) m' + ((q ^ e : ℕ) : ℤ) * Nat.gcdA (q ^ e) m') • x
        = x := by
      rw [show (m' : ℤ) * Nat.gcdB (q ^ e) m' + ((q ^ e : ℕ) : ℤ) * Nat.gcdA (q ^ e) m'
            = (1 : ℤ) from by rw [add_comm]; exact hg.symm, one_zsmul]
    exact ((add_smul _ _ x).symm.trans hone).symm
  · have hc : ((q ^ e : ℕ) : ℤ) * ((m' : ℤ) * Nat.gcdB (q ^ e) m')
        = Nat.gcdB (q ^ e) m' * ((q ^ e * m' : ℕ) : ℤ) := by push_cast; ring
    rw [← natCast_zsmul (((m' : ℤ) * Nat.gcdB (q ^ e) m') • x) (q ^ e), ← mul_smul, hc,
      mul_smul, natCast_zsmul, hx, smul_zero]
  · have hc : ((m' : ℕ) : ℤ) * (((q ^ e : ℕ) : ℤ) * Nat.gcdA (q ^ e) m')
        = Nat.gcdA (q ^ e) m' * ((q ^ e * m' : ℕ) : ℤ) := by push_cast; ring
    rw [← natCast_zsmul ((((q ^ e : ℕ) : ℤ) * Nat.gcdA (q ^ e) m') • x) m', ← mul_smul, hc,
      mul_smul, natCast_zsmul, hx, smul_zero]

private theorem n3red_target_primary (I : Ideal R)
    (hft : ∀ y : N, ∃ m : ℕ, 0 < m ∧ m • y = 0) (q : ℕ) (hq : q.Prime)
    {y : N} (hy : y ∈ I • (⊤ : Submodule R N)) (hqt : ∃ n : ℕ, q ^ n • y = 0) :
    y ∈ I • n3redQTors R N q := by
  have key : ∃ w ∈ I • n3redQTors R N q, ∃ c : ℕ, ¬ q ∣ c ∧ c • (y - w) = 0 := by
    refine Submodule.smul_induction_on hy (fun a ha v _ => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
    · obtain ⟨Mv, hMv0, hMv⟩ := hft v
      have hfac : q ^ Mv.factorization q * ordCompl[q] Mv = Mv :=
        Nat.ordProj_mul_ordCompl_eq_self Mv q
      have hcop : Nat.Coprime (q ^ Mv.factorization q) (ordCompl[q] Mv) :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hMv0.ne')
      obtain ⟨c₁, c₂, hsum, hc₁, hc₂⟩ :=
        n3red_bezout_split q (Mv.factorization q) (ordCompl[q] Mv) hcop v
          (by rw [hfac]; exact hMv)
      refine ⟨a • (c₁ • v),
        Submodule.smul_mem_smul ha (n3redQTors_mem.mpr ⟨Mv.factorization q, hc₁⟩),
        ordCompl[q] Mv, Nat.not_dvd_ordCompl hq hMv0.ne', ?_⟩
      have hv2 : v - c₁ • v = c₂ • v := sub_eq_iff_eq_add'.mpr hsum
      rw [← smul_sub, hv2, ← n3red_smul_nat_comm, hc₂, smul_zero]
    · obtain ⟨w₁, hw₁, c₁, hc₁q, hc₁⟩ := h₁
      obtain ⟨w₂, hw₂, c₂, hc₂q, hc₂⟩ := h₂
      refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, c₁ * c₂, ?_, ?_⟩
      · intro hd
        rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
        · exact hc₁q h
        · exact hc₂q h
      · have hre : y₁ + y₂ - (w₁ + w₂) = y₁ - w₁ + (y₂ - w₂) := by abel
        have k1 : (c₁ * c₂) • (y₁ - w₁) = 0 := by rw [mul_comm, mul_smul, hc₁, smul_zero]
        have k2 : (c₁ * c₂) • (y₂ - w₂) = 0 := by rw [mul_smul, hc₂, smul_zero]
        rw [hre, smul_add, k1, k2, add_zero]
  obtain ⟨w, hw, c, hcq, hc⟩ := key
  obtain ⟨n, hn⟩ := hqt
  obtain ⟨nw, hnw⟩ := n3redQTors_mem.mp (Submodule.smul_le_right hw)
  have hK : q ^ (n + nw) • (y - w) = 0 := by
    have hy0 : q ^ (n + nw) • y = 0 := by rw [pow_add, mul_comm, mul_smul, hn, smul_zero]
    have hw0 : q ^ (n + nw) • w = 0 := by rw [pow_add, mul_smul, hnw, smul_zero]
    rw [smul_sub, hy0, hw0, sub_zero]
  have hcop : Nat.Coprime (q ^ (n + nw)) c :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hcq)
  have hyw : y - w = 0 := n3red_coprime_kill _ _ hcop hK hc
  rw [sub_eq_zero] at hyw
  rw [hyw]
  exact hw

private theorem n3red_lift_primary (I : Ideal R) (f : M →ₗ[R] N) (q : ℕ)
    (htbq : ∀ y : N, (∃ n : ℕ, q ^ n • y = 0) → ∃ x : M, (∃ n : ℕ, q ^ n • x = 0) ∧ f x = y) :
    I • n3redQTors R N q ≤ (I • n3redQTors R M q).map f := by
  have hle : n3redQTors R N q ≤ (n3redQTors R M q).map f := by
    intro y hy
    obtain ⟨x, hx, hfx⟩ := htbq y (n3redQTors_mem.mp hy)
    exact Submodule.mem_map.mpr ⟨x, n3redQTors_mem.mpr hx, hfx⟩
  calc I • n3redQTors R N q ≤ I • (n3redQTors R M q).map f :=
        smul_mono_right I hle
    _ = (I • n3redQTors R M q).map f := (Submodule.map_smul'' I _ f).symm

private theorem n3red_crux (I : Ideal R) (f : M →ₗ[R] N) (ℓ q : ℕ) (hq : q.Prime) (hqℓ : q ≠ ℓ)
    (htb : ∀ q' : ℕ, q'.Prime → q' ≠ ℓ → ∀ y : N, (∃ n : ℕ, q' ^ n • y = 0) →
      ∃ x : M, (∃ n : ℕ, q' ^ n • x = 0) ∧ f x = y)
    (hinj : ∀ q' : ℕ, q'.Prime → q' ≠ ℓ → ∀ x : M, (∃ n : ℕ, q' ^ n • x = 0) → f x = 0 → x = 0)
    (hft : ∀ y : N, ∃ m : ℕ, 0 < m ∧ m • y = 0)
    {u : M} (hu : ∃ n : ℕ, q ^ n • u = 0)
    (hfu : f u ∈ (I • (⊤ : Submodule R M)).map f) :
    u ∈ I • (⊤ : Submodule R M) := by
  have h1 : f u ∈ I • (⊤ : Submodule R N) := by
    have hle : (I • (⊤ : Submodule R M)).map f ≤ I • (⊤ : Submodule R N) := by
      rw [Submodule.map_smul'']
      exact smul_mono_right I le_top
    exact hle hfu
  have h2 : ∃ n : ℕ, q ^ n • f u = 0 := by
    obtain ⟨n, hn⟩ := hu
    exact ⟨n, by rw [← map_nsmul, hn, map_zero]⟩
  have h3 : f u ∈ I • n3redQTors R N q := n3red_target_primary I hft q hq h1 h2
  obtain ⟨t, ht, hftu⟩ := Submodule.mem_map.mp (n3red_lift_primary I f q (htb q hq hqℓ) h3)
  have ht_tors : t ∈ n3redQTors R M q := Submodule.smul_le_right ht
  have ht_top : t ∈ I • (⊤ : Submodule R M) :=
    (smul_mono_right I (le_top : n3redQTors R M q ≤ ⊤)) ht
  obtain ⟨n₁, hn₁⟩ := hu
  obtain ⟨n₂, hn₂⟩ := n3redQTors_mem.mp ht_tors
  have hut : ∃ n : ℕ, q ^ n • (u - t) = 0 := by
    refine ⟨n₁ + n₂, ?_⟩
    have a1 : q ^ (n₁ + n₂) • u = 0 := by rw [pow_add, mul_comm, mul_smul, hn₁, smul_zero]
    have a2 : q ^ (n₁ + n₂) • t = 0 := by rw [pow_add, mul_smul, hn₂, smul_zero]
    rw [smul_sub, a1, a2, sub_zero]
  have hz : u - t = 0 := hinj q hq hqℓ _ hut (by rw [map_sub, hftu, sub_self])
  rw [sub_eq_zero] at hz
  rw [hz]
  exact ht_top

private theorem n3red_master (I : Ideal R) (f : M →ₗ[R] N) (ℓ : ℕ)
    (htb : ∀ q' : ℕ, q'.Prime → q' ≠ ℓ → ∀ y : N, (∃ n : ℕ, q' ^ n • y = 0) →
      ∃ x : M, (∃ n : ℕ, q' ^ n • x = 0) ∧ f x = y)
    (hinj : ∀ q' : ℕ, q'.Prime → q' ≠ ℓ → ∀ x : M, (∃ n : ℕ, q' ^ n • x = 0) → f x = 0 → x = 0)
    (hft : ∀ y : N, ∃ m : ℕ, 0 < m ∧ m • y = 0) :
    ∀ m : ℕ, ¬ ℓ ∣ m → ∀ u : M, m • u = 0 → f u ∈ (I • (⊤ : Submodule R M)).map f →
      u ∈ I • (⊤ : Submodule R M) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm u hu hfu
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [one_nsmul] at hu
      rw [hu]
      exact Submodule.zero_mem _
    · have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero ℓ)
      have hq : m.minFac.Prime := Nat.minFac_prime hm1
      have hqdvd : m.minFac ∣ m := Nat.minFac_dvd m
      have hqℓ : m.minFac ≠ ℓ := by rintro h; rw [← h] at hm; exact hm hqdvd
      have hfac : m.minFac ^ m.factorization m.minFac * ordCompl[m.minFac] m = m :=
        Nat.ordProj_mul_ordCompl_eq_self m m.minFac
      have hcop : Nat.Coprime (m.minFac ^ m.factorization m.minFac) (ordCompl[m.minFac] m) :=
        Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hq hm0)
      obtain ⟨c₁, c₂, hsum, hc₁, hc₂⟩ :=
        n3red_bezout_split m.minFac (m.factorization m.minFac) (ordCompl[m.minFac] m) hcop u
          (by rw [hfac]; exact hu)
      have hp1 : c₁ • u ∈ I • (⊤ : Submodule R M) := by
        refine n3red_crux I f ℓ m.minFac hq hqℓ htb hinj hft ⟨m.factorization m.minFac, hc₁⟩ ?_
        rw [map_zsmul]
        exact zsmul_mem hfu c₁
      have he1 : 1 ≤ m.factorization m.minFac := Nat.Prime.factorization_pos_of_dvd hq hm0 hqdvd
      have hlt : ordCompl[m.minFac] m < m := by
        have h1 : 1 < m.minFac ^ m.factorization m.minFac :=
          Nat.one_lt_pow (by omega) hq.one_lt
        exact Nat.div_lt_self (Nat.pos_of_ne_zero hm0) h1
      have hndvd : ¬ ℓ ∣ ordCompl[m.minFac] m := by
        intro hd
        exact hm (hd.trans (Nat.ordCompl_dvd m m.minFac))
      have hp2 : c₂ • u ∈ I • (⊤ : Submodule R M) := by
        refine ih (ordCompl[m.minFac] m) hlt hndvd (c₂ • u) hc₂ ?_
        rw [map_zsmul]
        exact zsmul_mem hfu c₂
      have hadd := Submodule.add_mem _ hp1 hp2
      rwa [← hsum] at hadd

end AbstractHelpers

section Bridge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

private def n3red_inducedMap (P : Submodule R M) (f : M →ₗ[R] N) :
    (M ⧸ P) →ₗ[R] (N ⧸ P.map f) :=
  P.liftQ ((P.map f).mkQ.comp f) (by
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_map_of_mem hx))

private theorem n3red_inducedMap_mk (P : Submodule R M) (f : M →ₗ[R] N) (x : M) :
    n3red_inducedMap P f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

private theorem n3red_inducedMap_mk_eq_zero (P : Submodule R M) (f : M →ₗ[R] N) (x : M) :
    n3red_inducedMap P f (Submodule.Quotient.mk x) = 0 ↔ f x ∈ P.map f := by
  rw [n3red_inducedMap_mk, Submodule.Quotient.mk_eq_zero]

private theorem n3red_package {R : Type*} [CommRing R] {M N : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (f : M →ₗ[R] N) (ℓ : ℕ)
    (hdiv : ∀ m : ℤ, m ≠ 0 → ∀ x : M, ∃ y : M, m • y = x)
    (htb : ∀ q : ℕ, q.Prime → q ≠ ℓ → ∀ y : N, (∃ n : ℕ, q ^ n • y = 0) →
      ∃ x : M, (∃ n : ℕ, q ^ n • x = 0) ∧ f x = y)
    (hinj : ∀ q : ℕ, q.Prime → q ≠ ℓ → ∀ x : M, (∃ n : ℕ, q ^ n • x = 0) → f x = 0 → x = 0)
    (hft : ∀ y : N, ∃ m : ℕ, 0 < m ∧ m • y = 0)
    (P : Submodule R M) (hP : P = I • (⊤ : Submodule R M)) :
    ∃ (T : Type) (_ : AddCommGroup T) (s : (M ⧸ P) →+ T),
      (∀ x : M, s (Submodule.Quotient.mk x) = 0 ↔ f x ∈ P.map f) ∧
      (∀ z : M ⧸ P, (∃ m : ℕ, ¬ ℓ ∣ m ∧ m • z = 0) → s z = 0 → z = 0) := by
  refine ⟨N ⧸ P.map f, inferInstance, (n3red_inducedMap P f).toAddMonoidHom,
    fun x => n3red_inducedMap_mk_eq_zero P f x, ?_⟩
  rintro z ⟨m, hmℓ, hmz⟩ hsz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P z
  have hmx : m • x ∈ P := by
    rw [← Submodule.Quotient.mk_eq_zero P]
    have hmk : (Submodule.Quotient.mk (m • x) : M ⧸ P) = m • Submodule.Quotient.mk x :=
      map_nsmul P.mkQ.toAddMonoidHom m x
    rw [hmk]
    exact hmz
  have hm0 : m ≠ 0 := by rintro rfl; exact hmℓ (dvd_zero ℓ)
  obtain ⟨u, hu0, hxu⟩ := n3red_torsion_lift I hdiv m hm0 (hP ▸ hmx)
  have hmk : (Submodule.Quotient.mk u : M ⧸ P) = Submodule.Quotient.mk x := by
    rw [Submodule.Quotient.eq]
    rw [show u - x = -(x - u) from by abel, hP]
    exact Submodule.neg_mem _ hxu
  have hsu : (n3red_inducedMap P f).toAddMonoidHom (Submodule.Quotient.mk u) = 0 := by
    rw [hmk]; exact hsz
  have hfu : f u ∈ P.map f := (n3red_inducedMap_mk_eq_zero P f u).mp hsu
  rw [hP] at hfu
  have humem : u ∈ I • (⊤ : Submodule R M) :=
    n3red_master I f ℓ htb hinj hft m hmℓ u hu0 hfu
  rw [← hmk, Submodule.Quotient.mk_eq_zero, hP]
  exact humem

private theorem n3red_map_toAddSubgroup_iff (P : Submodule R M) (f : M →ₗ[R] N) (g : M →+ N)
    (hfg : ∀ x, f x = g x) (y : N) :
    y ∈ P.toAddSubgroup.map g ↔ y ∈ P.map f := by
  rw [AddSubgroup.mem_map, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hfg x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hfg x).symm⟩

end Bridge

set_option synthInstance.maxHeartbeats 320000 in

private theorem n3red_spKer_iff (p : ℕ) [NeZero p] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [iJ : Module HeckeAlg (JZero p)]
    [iT : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p))]
    (sp : JZero p →+ Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p))
    (spL : JZero p →ₗ[HeckeAlg] Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p))
    (hspL : ∀ x, spL x = sp x)
    (y : Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)) :
    y ∈ spKernelImage sp ↔ y ∈ (eisensteinKernelSubmodule p iJ).map spL :=
  n3red_map_toAddSubgroup_iff (eisensteinKernelSubmodule p iJ) spL sp hspL y

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 320000 in
theorem solution (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p)
    (hdiv : ∀ m : ℤ, m ≠ 0 → ∀ x : JZero p, ∃ y : JZero p, m • y = x)
    (hdoor : ∀ ℓ : ℕ, (hℓp : ℓ.Prime) → ℓ ≠ p →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        letI := heckeModuleBar p
        ∃ _ : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)),
        ∃ D : JZeroGoodReductionSpecialization A ℓ hℓp p,
          TorsBijFor ℓ D.sp ∧
          FTorsionFor (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p)) ∧
          RaynaudFor ℓ D.sp ∧ CuspRuleFor A D.sp) :
    MazurQuotientSpecialization p (heckeModuleBar p) := by
  have _ := hcomm
  unfold MazurQuotientSpecialization
  intro ℓ hℓ hℓp A hA
  obtain ⟨iT, D, htb, hft, hry, hcr⟩ := hdoor ℓ hℓ hℓp A hA
  letI := heckeModuleBar p
  letI := iT

  let spL : JZero p →ₗ[HeckeAlg] Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p) :=
    { toFun := D.sp, map_add' := D.sp.map_add, map_smul' := D.hecke_comm }
  have hspL : ∀ x : JZero p, spL x = D.sp x := fun _ => rfl

  have hpack := n3red_package (R := HeckeAlg) (M := JZero p)
      (N := Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) p))
      (eisensteinKernel (JZero p) (eisensteinIdeal p)) spL ℓ hdiv htb
      (fun q' hq' hq'ℓ x hx hfx => D.injective_torsion q' hq' hq'ℓ x hx hfx) hft
      (eisensteinKernelSubmodule p (heckeModuleBar p)) rfl
  obtain ⟨T, iTgt, s, hbridge, hinj'⟩ := hpack

  have bridge : ∀ x : JZero p,
      s (eisensteinQuotientMk p (heckeModuleBar p) x) = 0 ↔ D.sp x ∈ spKernelImage D.sp := by
    intro x
    refine (hbridge x).trans ?_
    exact (n3red_spKer_iff p D.sp spL hspL (spL x)).symm
  refine ⟨T, iTgt, s, ?_, ?_, ?_⟩
  ·
    intro z _ hm hs
    exact hinj' z hm hs
  ·
    intro h2 z hz hk hs
    refine hry h2 z hz hk (fun x hx => ?_)
    exact (bridge x).1 (hx ▸ hs)
  ·
    intro x j₁ j₂ hinf hzero hσ ho1 ho2 hv
    obtain ⟨c1, c2⟩ := hcr x j₁ j₂ hinf hzero hσ ho1 ho2 hv
    exact ⟨fun h => (bridge _).2 (c1 h), fun h => (bridge _).2 (c2 h)⟩

end

end S_ModularCurve_mazurQuotientSpecialization_heckeModuleBar_of_doorV2
end P2MW
export P2MW.S_ModularCurve_mazurQuotientSpecialization_heckeModuleBar_of_doorV2 (solution)
