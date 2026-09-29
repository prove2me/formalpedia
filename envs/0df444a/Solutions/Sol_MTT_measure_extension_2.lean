-- Prove2me | solution 2 for MTT.measure_extension
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T05:48:16.066051+00:00
-- url     : https://prove2.me/submissions/f35284a0-fb1e-42d8-910c-bd41e6728a95

import Mathlib
import Definitions.Def_MTT_Measures
import Theorems.Thm_MTT_distribution_relation
import Theorems.Thm_MTT_ordinary_disk_bound
import Theorems.Thm_MTT_ordinary_centered_disk_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
open Topology Metric

namespace P2M

variable {p : ℕ} [Fact p.Prime]

theorem one_lt_p : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt

/-- Two `p`-adic integers agreeing mod `p ^ n` are within `p ^ (-n)`. -/
theorem norm_sub_le_of_toZModPow_eq {n : ℕ} {x y : ℤ_[p]}
    (h : PadicInt.toZModPow n x = PadicInt.toZModPow n y) :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  refine (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr ?_
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
  exact h

theorem toZModPow_eq_of_norm_sub_le {n : ℕ} {x y : ℤ_[p]}
    (h : ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y := by
  have h2 : x - y ∈ Ideal.span {(p : ℤ_[p]) ^ n} :=
    (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mp h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h2
  exact h2

/-- The unit group of `ℤ_[p]`, viewed inside `ℤ_[p]`. -/
def unitSet : Set ℤ_[p] := {x | IsUnit x}

theorem isOpen_unitSet : IsOpen (unitSet (p := p)) := Units.isOpen

theorem isClosed_unitSet : IsClosed (unitSet (p := p)) := by
  rw [← isOpen_compl_iff]
  have hc : (unitSet (p := p))ᶜ = Metric.ball (0 : ℤ_[p]) 1 := by
    ext z
    simp [unitSet, PadicInt.not_isUnit_iff, Metric.mem_ball, dist_eq_norm]
  rw [hc]
  exact Metric.isOpen_ball

theorem isCompact_unitSet : IsCompact (unitSet (p := p)) := isClosed_unitSet.isCompact

open Classical in
/-- The unit underlying an invertible `p`-adic integer (junk value `1` otherwise). -/
def unitOf (x : ℤ_[p]) : (ℤ_[p])ˣ := if h : IsUnit x then h.unit else 1

theorem unitOf_val {x : ℤ_[p]} (h : IsUnit x) : ((unitOf x : (ℤ_[p])ˣ) : ℤ_[p]) = x := by
  classical
  rw [unitOf, dif_pos h]
  exact h.unit_spec

@[simp] theorem unitOf_unit (u : (ℤ_[p])ˣ) : unitOf ((u : ℤ_[p])) = u :=
  Units.ext (unitOf_val u.isUnit)

theorem continuousOn_unitOf : ContinuousOn (unitOf (p := p)) unitSet := by
  rw [_root_.continuousOn_iff']
  intro t ht
  refine ⟨Units.val '' t, Units.isOpenEmbedding_val.isOpenMap t ht, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image, unitSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx1, hx2⟩
    exact ⟨⟨unitOf x, hx1, unitOf_val hx2⟩, hx2⟩
  · rintro ⟨⟨u, hu, rfl⟩, hx2⟩
    exact ⟨by simpa using hu, hx2⟩

/-- A continuous function on the units, transported to `ℤ_[p]`. -/
def extOn (g : C((ℤ_[p])ˣ, ℂ_[p])) : ℤ_[p] → ℂ_[p] := fun x => g (unitOf x)

theorem continuousOn_extOn (g : C((ℤ_[p])ˣ, ℂ_[p])) :
    ContinuousOn (extOn g) unitSet :=
  g.continuous.comp_continuousOn continuousOn_unitOf

@[simp] theorem extOn_apply (g : C((ℤ_[p])ˣ, ℂ_[p])) (u : (ℤ_[p])ˣ) :
    extOn g ((u : ℤ_[p])) = g u := by
  rw [extOn, unitOf_unit]

theorem exists_pow_neg_lt {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, (p : ℝ) ^ (-(n : ℤ)) < δ := by
  have hlt : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_p (p := p))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hlt
  refine ⟨n, ?_⟩
  rwa [zpow_neg, zpow_natCast, ← inv_pow]

/-- Uniform continuity of a continuous function on the compact unit group, expressed
through the residue disks. -/
theorem exists_modulus (g : C((ℤ_[p])ˣ, ℂ_[p])) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ u v : (ℤ_[p])ˣ,
      PadicInt.toZModPow n ((u : ℤ_[p])) = PadicInt.toZModPow n ((v : ℤ_[p])) →
        ‖g u - g v‖ < ε := by
  have huc := isCompact_unitSet.uniformContinuousOn_of_continuous (continuousOn_extOn g)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, h⟩ := huc ε hε
  obtain ⟨n, hn⟩ := exists_pow_neg_lt (p := p) hδ
  refine ⟨n, fun u v huv => ?_⟩
  have h1 : dist ((u : ℤ_[p])) ((v : ℤ_[p])) < δ := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (norm_sub_le_of_toZModPow_eq huv) hn
  have h2 := h _ u.isUnit _ v.isUnit h1
  rwa [extOn_apply, extOn_apply, dist_eq_norm] at h2

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

/-- Residue disks in `ℤ_[p]` are clopen. -/
theorem isClopen_fiber (n : ℕ) (a : ZMod (p ^ n)) :
    IsClopen {y : ℤ_[p] | PadicInt.toZModPow n y = a} := by
  have hr : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := by
    have := one_lt_p (p := p); positivity
  have key : ∀ (S : Set ℤ_[p]),
      (∀ y z : ℤ_[p], PadicInt.toZModPow n y = PadicInt.toZModPow n z → (y ∈ S ↔ z ∈ S)) →
      IsOpen S := by
    intro S hS
    rw [Metric.isOpen_iff]
    intro y hy
    refine ⟨_, hr, fun z hz => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact (hS z y (toZModPow_eq_of_norm_sub_le hz.le)).mpr hy
  constructor
  · rw [← isOpen_compl_iff]
    refine key _ fun y z h => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, h]
  · refine key _ fun y z h => ?_
    simp only [Set.mem_setOf_eq, h]

/-- The characteristic function of a residue disk, as a continuous map on the units. -/
def indCM (n : ℕ) (a : ZMod (p ^ n)) : C((ℤ_[p])ˣ, ℂ_[p]) where
  toFun x := if PadicInt.toZModPow n ((x : ℤ_[p])) = a then 1 else 0
  continuous_toFun := by
    classical
    have hclopen : IsClopen {x : (ℤ_[p])ˣ | PadicInt.toZModPow n ((x : ℤ_[p])) = a} := by
      have h := isClopen_fiber (p := p) n a
      exact ⟨h.1.preimage Units.continuous_val, h.2.preimage Units.continuous_val⟩
    refine Continuous.if ?_ continuous_const continuous_const
    intro x hx
    rw [hclopen.frontier_eq] at hx
    exact absurd hx (Set.notMem_empty x)

/-- The tautological coordinate, as a continuous map. -/
def coordCM : C((ℤ_[p])ˣ, ℂ_[p]) where
  toFun x := MTT.coordinate x
  continuous_toFun := by
    unfold MTT.coordinate
    fun_prop

/-- A continuous representative of `MTT.diskFunction`. -/
def diskCM (n : ℕ) (a : ZMod (p ^ n)) (j : ℕ) : C((ℤ_[p])ˣ, ℂ_[p]) :=
  indCM n a * coordCM ^ j

theorem diskCM_apply (n : ℕ) (a : ℤ) (j : ℕ) (x : (ℤ_[p])ˣ) :
    diskCM n ((a : ZMod (p ^ n))) j x = MTT.diskFunction n a j x := by
  classical
  simp only [diskCM, MTT.diskFunction, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
    indCM, coordCM, ContinuousMap.coe_mk]
  split <;> simp

end P2M

namespace P2M

/-- Representatives of the residue disks of depth `n` meeting the units. -/
def Idx (p n : ℕ) : Finset ℕ := (Finset.range (p ^ n)).filter (fun b => ¬ (p ∣ b))

theorem mem_Idx {p n b : ℕ} : b ∈ Idx p n ↔ b < p ^ n ∧ ¬ (p ∣ b) := by
  classical
  simp [Idx, Finset.mem_filter, Finset.mem_range]

variable {p : ℕ} [Fact p.Prime]

theorem isUnit_natCast {b : ℕ} (h : ¬ (p ∣ b)) : IsUnit ((b : ℤ_[p])) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
  intro hlt
  rw [show ((b : ℕ) : ℤ_[p]) = (((b : ℤ) : ℤ_[p])) by push_cast; ring,
    PadicInt.norm_int_lt_one_iff_dvd] at hlt
  exact h (by exact_mod_cast hlt)

/-- The unit of `ℤ_[p]` represented by a natural number prime to `p`. -/
def uNat (b : ℕ) : (ℤ_[p])ˣ := unitOf ((b : ℤ_[p]))

theorem uNat_val {b : ℕ} (h : ¬ (p ∣ b)) :
    ((uNat (p := p) b : (ℤ_[p])ˣ) : ℤ_[p]) = (b : ℤ_[p]) :=
  unitOf_val (isUnit_natCast h)

theorem toZModPow_uNat {n b : ℕ} (h : ¬ (p ∣ b)) :
    PadicInt.toZModPow n ((uNat (p := p) b : ℤ_[p])) = (b : ZMod (p ^ n)) := by
  rw [uNat_val h, map_natCast]

theorem coord_uNat {b : ℕ} (h : ¬ (p ∣ b)) :
    MTT.coordinate (uNat (p := p) b) = (b : ℂ_[p]) := by
  unfold MTT.coordinate
  rw [uNat_val h]
  push_cast
  simp

/-- Refinement: the depth-`n+1` disks meeting the units are the `p` refinements of the
depth-`n` ones. -/
theorem sum_Idx_succ {M : Type*} [AddCommMonoid M] {n : ℕ} (hn : 0 < n) (F : ℕ → M) :
    ∑ b' ∈ Idx p (n + 1), F b'
      = ∑ b ∈ Idx p n, ∑ c ∈ Finset.range p, F (b + c * p ^ n) := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpn : 0 < p ^ n := pow_pos hp0 n
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun b' => (b' % p ^ n, b' / p ^ n))
    (j := fun q : ℕ × ℕ => q.1 + q.2 * p ^ n) ?_ ?_ ?_ ?_ ?_
  · intro b' hb'
    rw [mem_Idx] at hb'
    rw [Finset.mem_product, mem_Idx, Finset.mem_range]
    refine ⟨⟨Nat.mod_lt _ hpn, ?_⟩, ?_⟩
    · intro hd
      refine hb'.2 ?_
      have hsplit : p ^ n * (b' / p ^ n) + b' % p ^ n = b' := Nat.div_add_mod _ _
      have hp1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
      exact hsplit ▸ Nat.dvd_add (Dvd.dvd.mul_right hp1 _) hd
    · have h1 := hb'.1
      rw [pow_succ] at h1
      exact Nat.div_lt_of_lt_mul (by omega)
  · rintro ⟨b, c⟩ hq
    rw [Finset.mem_product, mem_Idx, Finset.mem_range] at hq
    dsimp only at hq ⊢
    rw [mem_Idx]
    refine ⟨?_, ?_⟩
    · have h1 : b < p ^ n := hq.1.1
      have h2 : c < p := hq.2
      have h3 : c * p ^ n ≤ (p - 1) * p ^ n := Nat.mul_le_mul_right _ (by omega)
      have hpm : (p - 1) + 1 = p := by omega
      have h4 : p ^ n + (p - 1) * p ^ n = p * p ^ n := by
        calc p ^ n + (p - 1) * p ^ n = ((p - 1) + 1) * p ^ n := by ring
          _ = p * p ^ n := by rw [hpm]
      have h5 : p * p ^ n = p ^ (n + 1) := by rw [pow_succ]; ring
      omega
    · intro hd
      refine hq.1.2 ?_
      have hp1 : p ∣ c * p ^ n := Dvd.dvd.mul_left (dvd_pow_self p hn.ne') c
      have := Nat.dvd_sub hd hp1
      simpa using this
  · intro b' _
    dsimp only
    have h := Nat.div_add_mod b' (p ^ n)
    have h2 : b' / p ^ n * p ^ n = p ^ n * (b' / p ^ n) := Nat.mul_comm _ _
    omega
  · rintro ⟨b, c⟩ hq
    rw [Finset.mem_product, mem_Idx, Finset.mem_range] at hq
    dsimp only at hq ⊢
    have h1 : b < p ^ n := hq.1.1
    have e1 : (b + c * p ^ n) % p ^ n = b := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
    have e2 : (b + c * p ^ n) / p ^ n = c := by
      rw [Nat.add_mul_div_right _ _ hpn, Nat.div_eq_of_lt h1, zero_add]
    simp [e1, e2]
  · intro b' _
    dsimp only
    have h := Nat.div_add_mod b' (p ^ n)
    have h2 : b' / p ^ n * p ^ n = p ^ n * (b' / p ^ n) := Nat.mul_comm _ _
    congr 1
    omega

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

/-- In an ultrametric space a finite sum is no larger than its largest term. -/
theorem norm_sum_le_ultra {J : Type*} {C : ℝ} (hC : 0 ≤ C) (F : J → ℂ_[p]) :
    ∀ s : Finset J, (∀ i ∈ s, ‖F i‖ ≤ C) → ‖∑ i ∈ s, F i‖ ≤ C := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simpa using hC
  | insert a s ha ih =>
      intro h
      rw [Finset.sum_insert ha]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
        (max_le (h a (Finset.mem_insert_self a s))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)

/-- The disk moment attached to a natural-number representative. -/
def Mom (j n b : ℕ) : ℂ_[p] := MTT.diskMoment f ιp P α sg j n (b : ℤ)

variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

include hN hk hα in
theorem Mom_refine {j : ℕ} (hj : j ≤ k - 2) {n : ℕ} (hn : 0 < n) (b : ℕ) :
    ∑ c ∈ Finset.range p, Mom ιp f P α sg j (n + 1) (b + c * p ^ n)
      = Mom ιp f P α sg j n b := by
  simp only [Mom]
  have hd := MTT.distribution_relation hN hk ι ιp f P α hα sg j hj n hn (b : ℤ)
  rw [← hd]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1

/-- The `n`-th Riemann sum of `g` against the disk masses. -/
def RS (g : C((ℤ_[p])ˣ, ℂ_[p])) (n : ℕ) : ℂ_[p] :=
  ∑ b ∈ Idx p n, g (uNat b) * Mom ιp f P α sg 0 n b

include hN hk hα in
theorem RS_succ_sub (g : C((ℤ_[p])ˣ, ℂ_[p])) {n : ℕ} (hn : 0 < n) :
    RS ιp f P α sg g (n + 1) - RS ιp f P α sg g n
      = ∑ b ∈ Idx p n, ∑ c ∈ Finset.range p,
          (g (uNat (b + c * p ^ n)) - g (uNat b)) * Mom ιp f P α sg 0 (n + 1) (b + c * p ^ n) := by
  have h1 : RS ιp f P α sg g (n + 1)
      = ∑ b ∈ Idx p n, ∑ c ∈ Finset.range p,
          g (uNat (b + c * p ^ n)) * Mom ιp f P α sg 0 (n + 1) (b + c * p ^ n) := by
    show (∑ b' ∈ Idx p (n + 1), g (uNat b') * Mom ιp f P α sg 0 (n + 1) b') = _
    exact sum_Idx_succ hn (fun b' => g (uNat b') * Mom ιp f P α sg 0 (n + 1) b')
  have h2 : RS ιp f P α sg g n
      = ∑ b ∈ Idx p n, ∑ c ∈ Finset.range p,
          g (uNat b) * Mom ιp f P α sg 0 (n + 1) (b + c * p ^ n) := by
    show (∑ b ∈ Idx p n, g (uNat b) * Mom ιp f P α sg 0 n b) = _
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, Mom_refine ιp f P α sg hN hk hα (Nat.zero_le _) hn b]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

theorem not_dvd_add {n b c : ℕ} (hn : 0 < n) (hb : ¬ p ∣ b) : ¬ p ∣ (b + c * p ^ n) := by
  intro hd
  have hp1 : p ∣ c * p ^ n := Dvd.dvd.mul_left (dvd_pow_self p hn.ne') c
  exact hb (by simpa using Nat.dvd_sub hd hp1)

theorem natCast_add_mul_pow (n b c : ℕ) :
    (((b + c * p ^ n : ℕ)) : ZMod (p ^ n)) = ((b : ℕ) : ZMod (p ^ n)) := by
  push_cast
  rw [show ((p : ZMod (p ^ n))) ^ n = 0 by rw [← Nat.cast_pow, ZMod.natCast_self]]
  ring

theorem modulus_mono {n₀ n : ℕ} (h : n₀ ≤ n) {x y : ℤ_[p]}
    (hxy : PadicInt.toZModPow n x = PadicInt.toZModPow n y) :
    PadicInt.toZModPow n₀ x = PadicInt.toZModPow n₀ y := by
  refine toZModPow_eq_of_norm_sub_le (le_trans (norm_sub_le_of_toZModPow_eq hxy) ?_)
  have h1 : (1 : ℝ) ≤ (p : ℝ) := (one_lt_p (p := p)).le
  exact zpow_le_zpow_right₀ h1 (by omega)

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

theorem norm_sub_le_max' (a b c : ℂ_[p]) : ‖a - b‖ ≤ max ‖a - c‖ ‖b - c‖ := by
  have e : a - b = (a - c) + (-(b - c)) := by ring
  rw [e]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
  rw [norm_neg]

theorem norm_sub_le_of_steps (F : ℕ → ℂ_[p]) {C : ℝ} (hC : 0 ≤ C) (N₀ : ℕ)
    (h : ∀ m, N₀ ≤ m → ‖F (m + 1) - F m‖ ≤ C) : ∀ m, N₀ ≤ m → ‖F m - F N₀‖ ≤ C := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simpa using hC
  | succ m hm ih =>
      have e : F (m + 1) - F N₀ = (F (m + 1) - F m) + (F m - F N₀) := by ring
      rw [e]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (h m hm) ih)

variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

include hN hk hα in
theorem exists_mass_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → ∀ b : ℕ,
    ‖Mom ιp f P α sg 0 n b‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := MTT.ordinary_disk_bound hN hk ι ιp f P α hα
  exact ⟨C, hC0, fun n hn b => hC sg n hn (b : ℤ)⟩

include hN hk hα in
theorem RS_step_bound (g : C((ℤ_[p])ˣ, ℂ_[p])) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hM : ∀ (n : ℕ), 0 < n → ∀ b : ℕ, ‖Mom ιp f P α sg 0 n b‖ ≤ C)
    {n : ℕ} (hn : 0 < n)
    (hmod : ∀ u v : (ℤ_[p])ˣ,
      PadicInt.toZModPow n ((u : ℤ_[p])) = PadicInt.toZModPow n ((v : ℤ_[p])) →
        ‖g u - g v‖ ≤ ε) :
    ‖RS ιp f P α sg g (n + 1) - RS ιp f P α sg g n‖ ≤ ε * C := by
  rw [RS_succ_sub ιp f P α sg hN hk hα g hn]
  refine norm_sum_le_ultra (by positivity) _ _ fun b hb => ?_
  refine norm_sum_le_ultra (by positivity) _ _ fun c _ => ?_
  rw [norm_mul]
  rw [mem_Idx] at hb
  refine mul_le_mul (hmod _ _ ?_) (hM (n + 1) (by omega) _) (norm_nonneg _) hε
  rw [toZModPow_uNat (not_dvd_add hn hb.2), toZModPow_uNat hb.2, natCast_add_mul_pow]

include hN hk hα in
theorem cauchySeq_RS (g : C((ℤ_[p])ˣ, ℂ_[p])) :
    CauchySeq (fun n => RS ιp f P α sg g (n + 1)) := by
  obtain ⟨C, hC0, hM⟩ := exists_mass_bound ιp f P α sg hN hk hα
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set ε' : ℝ := ε / (2 * (C + 1)) with hε'def
  have hCpos : (0 : ℝ) < C + 1 := by linarith
  have hε'pos : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨n₀, hn₀⟩ := exists_modulus (p := p) g hε'pos
  have hlt : ε' * C < ε := by
    rw [hε'def]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hstep : ∀ m, n₀ ≤ m →
      ‖RS ιp f P α sg g (m + 1 + 1) - RS ιp f P α sg g (m + 1)‖ ≤ ε' * C := by
    intro m hm
    refine RS_step_bound ιp f P α sg hN hk hα g hC0 hε'pos.le hM (by omega) ?_
    intro u v huv
    exact (hn₀ u v (modulus_mono (by omega) huv)).le
  have htel := norm_sub_le_of_steps (fun m => RS ιp f P α sg g (m + 1))
    (by positivity : (0:ℝ) ≤ ε' * C) n₀ hstep
  refine ⟨n₀, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (le_trans (norm_sub_le_max' _ _ _) (max_le (htel m hm) (htel n hn))) hlt

/-- The measure attached to `g`: the limit of its Riemann sums. -/
def MU (g : C((ℤ_[p])ˣ, ℂ_[p])) : ℂ_[p] :=
  Filter.limUnder Filter.atTop (fun n => RS ιp f P α sg g (n + 1))

include hN hk hα in
theorem tendsto_RS (g : C((ℤ_[p])ˣ, ℂ_[p])) :
    Filter.Tendsto (fun n => RS ιp f P α sg g (n + 1)) Filter.atTop
      (nhds (MU ιp f P α sg g)) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_RS ιp f P α sg hN hk hα g)
  simp only [MU, Filter.Tendsto.limUnder_eq hL]
  exact hL

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]
variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

theorem RS_add (g h : C((ℤ_[p])ˣ, ℂ_[p])) (n : ℕ) :
    RS ιp f P α sg (g + h) n = RS ιp f P α sg g n + RS ιp f P α sg h n := by
  simp only [RS, ContinuousMap.add_apply, add_mul]
  exact Finset.sum_add_distrib

theorem RS_smul (c : ℂ_[p]) (g : C((ℤ_[p])ˣ, ℂ_[p])) (n : ℕ) :
    RS ιp f P α sg (c • g) n = c * RS ιp f P α sg g n := by
  simp only [RS, ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem RS_norm_le (g : C((ℤ_[p])ˣ, ℂ_[p])) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ (n : ℕ), 0 < n → ∀ b : ℕ, ‖Mom ιp f P α sg 0 n b‖ ≤ C)
    {n : ℕ} (hn : 0 < n) : ‖RS ιp f P α sg g n‖ ≤ C * ‖g‖ := by
  refine norm_sum_le_ultra (by positivity) _ _ fun b _ => ?_
  rw [norm_mul, mul_comm]
  exact mul_le_mul (hM n hn b) (g.norm_coe_le_norm _) (norm_nonneg _) hC

include hN hk hα in
theorem MU_add (g h : C((ℤ_[p])ˣ, ℂ_[p])) :
    MU ιp f P α sg (g + h) = MU ιp f P α sg g + MU ιp f P α sg h := by
  refine tendsto_nhds_unique (tendsto_RS ιp f P α sg hN hk hα (g + h)) ?_
  have h2 := (tendsto_RS ιp f P α sg hN hk hα g).add
    (tendsto_RS ιp f P α sg hN hk hα h)
  refine h2.congr fun n => ?_
  exact (RS_add ιp f P α sg g h (n + 1)).symm

include hN hk hα in
theorem MU_smul (c : ℂ_[p]) (g : C((ℤ_[p])ˣ, ℂ_[p])) :
    MU ιp f P α sg (c • g) = c * MU ιp f P α sg g := by
  refine tendsto_nhds_unique (tendsto_RS ιp f P α sg hN hk hα (c • g)) ?_
  have h2 := (tendsto_RS ιp f P α sg hN hk hα g).const_mul c
  refine h2.congr fun n => ?_
  exact (RS_smul ιp f P α sg c g (n + 1)).symm

include hN hk hα in
theorem MU_norm_le (g : C((ℤ_[p])ˣ, ℂ_[p])) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ (n : ℕ), 0 < n → ∀ b : ℕ, ‖Mom ιp f P α sg 0 n b‖ ≤ C) :
    ‖MU ιp f P α sg g‖ ≤ C * ‖g‖ := by
  refine le_of_tendsto ((tendsto_RS ιp f P α sg hN hk hα g).norm)
    (Filter.Eventually.of_forall fun n => ?_)
  exact RS_norm_le ιp f P α sg g hC hM (Nat.succ_pos n)

end P2M

namespace P2M
section Analytic
open scoped ModularForm
open MeasureTheory Complex UpperHalfPlane MTT ModularForm ConjAct Pointwise

variable {N k : ℕ} {ι : Qbar →+* ℂ}

/-- `∫_0^∞ f(r + iy) y^j dy`. -/
def verticalMoment (f : UpperHalfPlane → ℂ) (r : ℚ) (j : ℕ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j

theorem rational_translate_integrable {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    IntegrableOn (fun t : ℝ =>
      f (ofComplex ((r : ℂ) + Complex.I * t)) * (t : ℂ) ^ j) (Set.Ioi 0) := by
  let : NeZero N := ⟨by omega⟩
  let g : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.upperRightHom r
  let gr : GL (Fin 2) ℝ := g.map (Rat.castHom ℝ)
  have hr : gr = Matrix.GeneralLinearGroup.upperRightHom (r : ℝ) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [gr, g]
  let : (GammaOne N).IsArithmetic := by dsimp [GammaOne]; infer_instance
  let : (toConjAct gr⁻¹ • GammaOne N).IsArithmetic := by
    have hh := Subgroup.IsArithmetic.conj (GammaOne N) g⁻¹
    simpa [gr] using hh
  let F := CuspForm.translate f gr
  have hconv := ((CuspForm.isStrongFEPair (by omega : (0 : ℤ) < k) F).hasMellin
    ((j : ℂ) + 1)).1
  unfold MellinConvergent at hconv
  have hval (t : ℝ) (ht : 0 < t) :
      F (ofComplex (Complex.I * t)) = f (ofComplex ((r : ℂ) + Complex.I * t)) := by
    change (⇑f ∣[(k : ℤ)] gr) _ = _
    rw [slash_def, hr]
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    simp [σ, denom, Matrix.GeneralLinearGroup.upperRightHom]
    congr 1
    ext
    simp [coe_smul, σ, num, denom, ofComplex_apply_of_im_pos, ht]
    ring
  apply hconv.congr_fun _ measurableSet_Ioi
  intro t ht
  simp only [ModularForm.weakFEPair, add_sub_cancel_right, Complex.cpow_natCast,
    smul_eq_mul, hval t ht]
  ring

theorem vm_periodic (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) :
    verticalMoment f (r + 1) j = verticalMoment f r j := by
  have hp := SlashInvariantFormClass.periodic_comp_ofComplex f
    (show (1 : ℝ) ∈ (GammaOne N).strictPeriods by
      simp [GammaOne, CongruenceSubgroup.strictPeriods_Gamma1])
  unfold verticalMoment
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  apply congrArg (fun z : ℂ => z * (t : ℂ) ^ j)
  simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using
    hp ((r : ℂ) + Complex.I * t)

theorem modularIntegral_pow (hN : 0 < N) (hk : 2 ≤ k)
    (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (t : ℕ) :
    modularIntegral f (Polynomial.X ^ t) r
      = 2 * (Real.pi : ℂ) * ∑ l ∈ Finset.range (t + 1),
          (Complex.I ^ l * (r : ℂ) ^ (t - l) * (t.choose l : ℂ)) * verticalMoment f r l := by
  set g : ℕ → ℝ → ℂ := fun l x =>
      (Complex.I ^ l * (r : ℂ) ^ (t - l) * (t.choose l : ℂ)) *
        (f (ofComplex ((r : ℂ) + Complex.I * x)) * (x : ℂ) ^ l) with hg
  have hgint : ∀ l ∈ Finset.range (t + 1), IntegrableOn (g l) (Set.Ioi 0) := by
    intro l _
    exact (rational_translate_integrable hN hk f r l).const_mul _
  have hpt : ∀ x : ℝ,
      f (ofComplex ((r : ℂ) + Complex.I * x)) *
          (Polynomial.X ^ t : Polynomial ℂ).eval ((r : ℂ) + Complex.I * x)
      = ∑ l ∈ Finset.range (t + 1), g l x := by
    intro x
    simp only [hg, Polynomial.eval_pow, Polynomial.eval_X]
    rw [add_comm ((r : ℂ)) (Complex.I * x), add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow]
    ring
  unfold modularIntegral
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x),
    MeasureTheory.integral_finsetSum (Finset.range (t + 1)) hgint]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hg]
  rw [MeasureTheory.integral_const_mul]
  simp only [verticalMoment]

/-- Binomial inversion: recentring the shifted moments at `a` recovers `m ^ j * V j`. -/
theorem centered_collapse {R : Type*} [CommRing R] (V : ℕ → R) (m a : R) (j : ℕ) :
    (∑ t ∈ Finset.range (j + 1), (j.choose t : R) * (-a) ^ (j - t) *
      (∑ u ∈ Finset.range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u))
      = m ^ j * V j := by
  have step1 : ∀ t ∈ Finset.range (j + 1),
      (j.choose t : R) * (-a) ^ (j - t) *
        (∑ u ∈ Finset.range (t + 1), (t.choose u : R) * m ^ u * a ^ (t - u) * V u)
      = ∑ u ∈ Finset.range (t + 1),
          ((j.choose t : R) * (t.choose u : R)) *
            ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u) := by
    intro t _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [Finset.sum_congr rfl step1]
  rw [Finset.sum_comm' (t' := Finset.range (j + 1)) (s' := fun u => Finset.Ico u (j + 1))
      (h := by intro x y; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have inner : ∀ u ∈ Finset.range (j + 1),
      (∑ t ∈ Finset.Ico u (j + 1),
        ((j.choose t : R) * (t.choose u : R)) *
          ((-a) ^ (j - t) * a ^ (t - u) * m ^ u * V u))
      = (j.choose u : R) * m ^ u * V u * (0 : R) ^ (j - u) := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hu' : u ≤ j := Nat.lt_succ_iff.mp hu
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : j + 1 - u = (j - u) + 1 := by omega
    rw [hlen]
    have key : ∀ v ∈ Finset.range ((j - u) + 1),
        ((j.choose (u + v) : R) * ((u + v).choose u : R)) *
          ((-a) ^ (j - (u + v)) * a ^ ((u + v) - u) * m ^ u * V u)
        = ((j.choose u : R) * m ^ u * V u) *
            (a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) := by
      intro v hv
      rw [Finset.mem_range] at hv
      have hv' : v ≤ j - u := Nat.lt_succ_iff.mp hv
      have hch : j.choose (u + v) * (u + v).choose u = j.choose u * (j - u).choose v := by
        have := Nat.choose_mul (n := j) (k := u + v) (s := u) (Nat.le_add_right u v)
        simpa using this
      have h1 : j - (u + v) = (j - u) - v := by omega
      have h2 : (u + v) - u = v := by omega
      rw [h1, h2]
      have hcast : ((j.choose (u + v) : R) * ((u + v).choose u : R))
          = ((j.choose u : R) * ((j - u).choose v : R)) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) hch
      rw [hcast]; ring
    rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
    have hbin : (∑ v ∈ Finset.range ((j - u) + 1),
        a ^ v * (-a) ^ ((j - u) - v) * ((j - u).choose v : R)) = (0 : R) ^ (j - u) := by
      rw [← add_pow]; simp
    rw [hbin]
  rw [Finset.sum_congr rfl inner, Finset.sum_eq_single j]
  · simp
  · intro u hu hne
    rw [Finset.mem_range] at hu
    have : j - u ≠ 0 := by omega
    simp [zero_pow this]
  · intro h
    exact absurd (Finset.self_mem_range_succ j) h

theorem collapse_MI (hN : 0 < N) (hk : 2 ≤ k) (f : CuspForm (GammaOne N) (k : ℤ))
    (j : ℕ) (a m : ℚ) (c : ℂ) (r : ℚ)
    (hr : ∀ t l : ℕ, l ≤ t →
      (m : ℂ) ^ t * c ^ t * ((r : ℂ) ^ (t - l) * Complex.I ^ l)
        = (-(a : ℂ)) ^ (t - l) * (c * Complex.I * (m : ℂ)) ^ l) :
    (∑ t ∈ Finset.range (j + 1),
      (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
        (c ^ t * modularIntegral f (Polynomial.X ^ t) r))
      = 2 * (Real.pi : ℂ) * (c * Complex.I * (m : ℂ)) ^ j * verticalMoment f r j := by
  have hL : (∑ t ∈ Finset.range (j + 1),
      (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
        (c ^ t * modularIntegral f (Polynomial.X ^ t) r))
      = 2 * (Real.pi : ℂ) * ∑ t ∈ Finset.range (j + 1),
          (j.choose t : ℂ) * (-(-(a : ℂ))) ^ (j - t) *
            (∑ l ∈ Finset.range (t + 1), (t.choose l : ℂ) *
              (c * Complex.I * (m : ℂ)) ^ l * (-(a : ℂ)) ^ (t - l) *
                verticalMoment f r l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [modularIntegral_pow hN hk f r t]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hlt : l ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    linear_combination ((j.choose t : ℂ) * (a : ℂ) ^ (j - t) * (2 * (Real.pi : ℂ)) *
      (t.choose l : ℂ) * verticalMoment f r l) * hr t l hlt
  rw [hL, centered_collapse (fun l => verticalMoment f r l) (c * Complex.I * (m : ℂ))
    (-(a : ℂ)) j]
  ring

theorem symbol_closed (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (a m : ℚ) (hm : m ≠ 0) :
    P.omega s * ι (algebraicSymbol P s j a m)
      = (Real.pi : ℂ) * (Complex.I * (m : ℂ)) ^ j *
          (verticalMoment f.form (-a / m) j +
            (MTT.sign s : ℂ) * (-1 : ℂ) ^ j * verticalMoment f.form (a / m) j) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hom := P.omega_ne s
  have hneg : -(-a / m : ℚ) = a / m := by field_simp
  have h1 : P.omega s * ι (algebraicSymbol P s j a m)
      = ∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
          signedIntegral f.form s t (-a / m) := by
    simp only [algebraicSymbol, map_sum, map_mul, map_pow, map_natCast, map_ratCast,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ k - 2 := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)) hj
    rw [P.comparison s t (-a / m) ht']
    field_simp
  have h2 : ∀ t : ℕ, signedIntegral f.form s t (-a / m)
      = (modularIntegral f.form (Polynomial.X ^ t) (-a / m)
          + (MTT.sign s : ℂ) * (-1 : ℂ) ^ t *
              modularIntegral f.form (Polynomial.X ^ t) (a / m)) / 2 := by
    intro t
    rw [signedIntegral, hneg]
  have hcol1 := collapse_MI hN hk f.form j a m 1 (-a / m) (by
    intro t l hlt
    have hml : (m : ℂ) ^ t = (m : ℂ) ^ l * (m : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [div_pow, hml]
    field_simp
    ring)
  have hcol2 := collapse_MI hN hk f.form j a m (-1) (a / m) (by
    intro t l hlt
    have hml : (m : ℂ) ^ t = (m : ℂ) ^ l * (m : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    have hsl : (-1 : ℂ) ^ t = (-1 : ℂ) ^ l * (-1 : ℂ) ^ (t - l) := by
      rw [← pow_add]; congr 1; omega
    push_cast
    rw [div_pow, hml, hsl]
    field_simp
    ring)
  have hsum_eq : (∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
      signedIntegral f.form s t (-a / m))
      = (∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
          ((1 : ℂ) ^ t * modularIntegral f.form (Polynomial.X ^ t) (-a / m))) / 2
        + (MTT.sign s : ℂ) *
          ((∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ) * (m : ℂ) ^ t * (a : ℂ) ^ (j - t) *
            (((-1) : ℂ) ^ t * modularIntegral f.form (Polynomial.X ^ t) (a / m))) / 2) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [h2 t]
    ring
  rw [h1, hsum_eq, hcol1, hcol2]
  ring

theorem vm_periodic_nat (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j n : ℕ) :
    verticalMoment f (r + n) j = verticalMoment f r j := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : (r + ((n + 1 : ℕ) : ℚ)) = (r + (n : ℚ)) + 1 := by push_cast; ring
      rw [hstep, vm_periodic, ih]

theorem vm_shift_sub (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j b : ℕ) :
    verticalMoment f (r - b) j = verticalMoment f r j := by
  have := vm_periodic_nat f (r - (b : ℚ)) j b
  rw [sub_add_cancel] at this
  exact this.symm

theorem symbol_shift (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (s : Bool) (j : ℕ) (hj : j ≤ k - 2)
    {p : ℕ} (hp : p.Prime) (n b : ℕ) (a : ℤ) :
    algebraicSymbol P s j ((a : ℚ) + (b : ℚ) * (p : ℚ) ^ n) ((p : ℚ) ^ n)
      = algebraicSymbol P s j (a : ℚ) ((p : ℚ) ^ n) := by
  have hpQ : ((p : ℚ)) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hme : ((p : ℚ) ^ n) ≠ 0 := pow_ne_zero n hpQ
  refine ι.injective ?_
  refine mul_left_cancel₀ (P.omega_ne s) ?_
  rw [symbol_closed hN hk f P s j hj _ _ hme, symbol_closed hN hk f P s j hj _ _ hme]
  have e1 : (-((a : ℚ) + (b : ℚ) * (p : ℚ) ^ n) / (p : ℚ) ^ n)
      = (-(a : ℚ) / (p : ℚ) ^ n) - (b : ℚ) := by field_simp; ring
  have e2 : (((a : ℚ) + (b : ℚ) * (p : ℚ) ^ n) / (p : ℚ) ^ n)
      = ((a : ℚ) / (p : ℚ) ^ n) + (b : ℚ) := by field_simp
  rw [e1, e2, vm_shift_sub f.form _ j b, vm_periodic_nat f.form _ j b]
end Analytic
end P2M

namespace P2M
section Periodicity
open scoped ModularForm
open MeasureTheory Complex UpperHalfPlane MTT ModularForm

variable {N k : ℕ} {ι : Qbar →+* ℂ}

theorem vm_periodic_int (f : CuspForm (GammaOne N) (k : ℤ)) (r : ℚ) (j : ℕ) (t : ℤ) :
    verticalMoment f (r + (t : ℚ)) j = verticalMoment f r j := by
  induction t using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have e : (r + (((n : ℤ) + 1 : ℤ) : ℚ)) = (r + ((n : ℤ) : ℚ)) + 1 := by push_cast; ring
      rw [e, vm_periodic, ih]
  | pred n ih =>
      have e : (r + ((-(n : ℤ) - 1 : ℤ) : ℚ)) = (r + ((-(n : ℤ) : ℤ) : ℚ)) - 1 := by
        push_cast; ring
      rw [e]
      have h2 := vm_periodic f ((r + ((-(n : ℤ) : ℤ) : ℚ)) - 1) j
      rw [sub_add_cancel] at h2
      rw [← h2, ih]

theorem symbol_shift_int (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (sg : Bool) (j : ℕ) (hj : j ≤ k - 2)
    (a m : ℚ) (hm : m ≠ 0) (t : ℤ) :
    algebraicSymbol P sg j (a + (t : ℚ) * m) m = algebraicSymbol P sg j a m := by
  refine ι.injective ?_
  refine mul_left_cancel₀ (P.omega_ne sg) ?_
  rw [symbol_closed hN hk f P sg j hj _ _ hm, symbol_closed hN hk f P sg j hj _ _ hm]
  have e1 : (-(a + (t : ℚ) * m) / m) = (-a / m) + (((-t : ℤ)) : ℚ) := by
    field_simp
    push_cast
    ring
  have e2 : ((a + (t : ℚ) * m) / m) = (a / m) + (((t : ℤ)) : ℚ) := by
    field_simp
  rw [e1, e2, vm_periodic_int, vm_periodic_int]

variable {p : ℕ} [Fact p.Prime]

theorem diskMoment_shift (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (P : Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
    (j : ℕ) (hj : j ≤ k - 2) {n : ℕ} (hn : 0 < n) (a t : ℤ) :
    diskMoment f ιp P α sg j n (a + t * (p : ℤ) ^ n) = diskMoment f ιp P α sg j n a := by
  have hpQ : ((p : ℚ)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).pos.ne'
  have h1 : ((p : ℚ)) ^ n ≠ 0 := pow_ne_zero _ hpQ
  have h2 : ((p : ℚ)) ^ (n - 1) ≠ 0 := pow_ne_zero _ hpQ
  have hpow : ((p : ℚ)) ^ n = (p : ℚ) * (p : ℚ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have E1 : algebraicSymbol P sg j (((a + t * (p : ℤ) ^ n : ℤ)) : ℚ) ((p : ℚ) ^ n)
      = algebraicSymbol P sg j ((a : ℤ) : ℚ) ((p : ℚ) ^ n) := by
    have e : (((a + t * (p : ℤ) ^ n : ℤ)) : ℚ)
        = ((a : ℤ) : ℚ) + ((t : ℤ) : ℚ) * ((p : ℚ) ^ n) := by push_cast; ring
    rw [e, symbol_shift_int hN hk f P sg j hj _ _ h1 t]
  have E2 : algebraicSymbol P sg j (((a + t * (p : ℤ) ^ n : ℤ)) : ℚ) ((p : ℚ) ^ (n - 1))
      = algebraicSymbol P sg j ((a : ℤ) : ℚ) ((p : ℚ) ^ (n - 1)) := by
    have e : (((a + t * (p : ℤ) ^ n : ℤ)) : ℚ)
        = ((a : ℤ) : ℚ) + ((t * (p : ℤ) : ℤ) : ℚ) * ((p : ℚ) ^ (n - 1)) := by
      push_cast
      rw [hpow]
      ring
    rw [e, symbol_shift_int hN hk f P sg j hj _ _ h2 (t * (p : ℤ))]
  simp only [diskMoment, E1, E2]

theorem diskMoment_congr (hN : 0 < N) (hk : 2 ≤ k) (f : Eigenform N k ι)
    (ιp : Qbar →+* ℂ_[p]) (P : Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
    (j : ℕ) (hj : j ≤ k - 2) {n : ℕ} (hn : 0 < n) {a a' : ℤ}
    (h : ((a : ℤ) : ZMod (p ^ n)) = ((a' : ℤ) : ZMod (p ^ n))) :
    diskMoment f ιp P α sg j n a = diskMoment f ιp P α sg j n a' := by
  have h0 : (((a - a' : ℤ)) : ZMod (p ^ n)) = 0 := by
    push_cast
    rw [h]
    ring
  have hdvd : (((p ^ n : ℕ)) : ℤ) ∣ (a - a') := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨t, ht⟩ := hdvd
  have he : a = a' + t * (p : ℤ) ^ n := by
    have : ((p ^ n : ℕ) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    rw [this] at ht
    linarith [ht]
  rw [he, diskMoment_shift hN hk f ιp P α sg j hj hn a' t]

end Periodicity
end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

instance neZero_pow (n : ℕ) : NeZero (p ^ n) := ⟨(pow_pos (Fact.out : p.Prime).pos n).ne'⟩

theorem natCast_add_mul_pow' {n m b c : ℕ} (h : n ≤ m) :
    (((b + c * p ^ m : ℕ)) : ZMod (p ^ n)) = ((b : ℕ) : ZMod (p ^ n)) := by
  push_cast
  have hz : ((p : ZMod (p ^ n))) ^ m = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p h
  rw [hz]
  ring

/-- The depth-`m` disks refining a given depth-`n` disk. -/
def Fib (p n : ℕ) (a : ZMod (p ^ n)) (m : ℕ) : Finset ℕ :=
  (Idx p m).filter (fun b => ((b : ℕ) : ZMod (p ^ n)) = a)

theorem Fib_self {n : ℕ} (hn : 0 < n) {a : ℤ} (ha : ¬ ((p : ℤ) ∣ a)) :
    Fib p n ((a : ZMod (p ^ n))) n = {((a : ZMod (p ^ n))).val} := by
  classical
  have hdvdpn : (p : ℤ) ∣ ((p : ℤ)) ^ n := dvd_pow_self _ hn.ne'
  ext b
  simp only [Fib, Finset.mem_filter, mem_Idx, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hb1, _⟩, hb2⟩
    rw [← hb2, ZMod.val_natCast_of_lt hb1]
  · rintro rfl
    have hval : (((((a : ZMod (p ^ n))).val : ℕ)) : ZMod (p ^ n)) = ((a : ZMod (p ^ n))) := by
      simp [ZMod.natCast_val, ZMod.cast_id]
    refine ⟨⟨ZMod.val_lt _, ?_⟩, hval⟩
    intro hd
    refine ha ?_
    have h0 : ((((((a : ZMod (p ^ n))).val : ℕ) : ℤ) - a : ℤ) : ZMod (p ^ n)) = 0 := by
      push_cast
      rw [hval]
      ring
    have hdd : (((p ^ n : ℕ)) : ℤ) ∣ ((((a : ZMod (p ^ n))).val : ℤ) - a) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have hpn : (((p ^ n : ℕ)) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    rw [hpn] at hdd
    have h1 : (p : ℤ) ∣ ((((a : ZMod (p ^ n))).val : ℤ) - a) := dvd_trans hdvdpn hdd
    have h2 : (p : ℤ) ∣ ((((a : ZMod (p ^ n))).val : ℤ)) := by exact_mod_cast hd
    have h3 : (p : ℤ) ∣ (((((a : ZMod (p ^ n))).val : ℤ)) -
        ((((a : ZMod (p ^ n))).val : ℤ) - a)) := dvd_sub h2 h1
    simpa using h3

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]
variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

include hN hk hα in
/-- Iterated refinement: the depth-`m` moments inside a depth-`n` disk sum to its moment. -/
theorem sum_fiber {j : ℕ} (hj : j ≤ k - 2) {n : ℕ} (hn : 0 < n) {a : ℤ}
    (ha : ¬ ((p : ℤ) ∣ a)) :
    ∀ m, n ≤ m → ∑ b ∈ Fib p n ((a : ZMod (p ^ n))) m, Mom ιp f P α sg j m b
      = MTT.diskMoment f ιp P α sg j n a := by
  classical
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
      rw [Fib_self hn ha, Finset.sum_singleton]
      simp only [Mom]
      refine diskMoment_congr hN hk f ιp P α sg j hj hn ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
  | succ m hm ih =>
      rw [← ih, Fib, Fib, Finset.sum_filter, Finset.sum_filter,
        sum_Idx_succ (show 0 < m by omega)
          (fun b' => if ((b' : ℕ) : ZMod (p ^ n)) = ((a : ZMod (p ^ n))) then
            Mom ιp f P α sg j (m + 1) b' else 0)]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hcond : ∀ c : ℕ, (((b + c * p ^ m : ℕ)) : ZMod (p ^ n)) = ((a : ZMod (p ^ n)))
          ↔ ((b : ℕ) : ZMod (p ^ n)) = ((a : ZMod (p ^ n))) := by
        intro c
        rw [natCast_add_mul_pow' hm]
      by_cases hb : ((b : ℕ) : ZMod (p ^ n)) = ((a : ZMod (p ^ n)))
      · have hall : ∀ c ∈ Finset.range p,
            (if (((b + c * p ^ m : ℕ)) : ZMod (p ^ n)) = ((a : ZMod (p ^ n)))
              then Mom ιp f P α sg j (m + 1) (b + c * p ^ m) else 0)
            = Mom ιp f P α sg j (m + 1) (b + c * p ^ m) := by
          intro c _
          rw [if_pos ((hcond c).mpr hb)]
        rw [Finset.sum_congr rfl hall, if_pos hb]
        exact Mom_refine ιp f P α sg hN hk hα hj (show 0 < m by omega) b
      · have hall : ∀ c ∈ Finset.range p,
            (if (((b + c * p ^ m : ℕ)) : ZMod (p ^ n)) = ((a : ZMod (p ^ n)))
              then Mom ιp f P α sg j (m + 1) (b + c * p ^ m) else 0) = 0 := by
          intro c _
          exact if_neg (fun h => hb ((hcond c).mp h))
        rw [Finset.sum_congr rfl hall, if_neg hb, Finset.sum_const_zero]

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have hcoe : (((p : ℚ_[p])) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; ring
  have h := PadicComplex.norm_extends' (p := p) ((p : ℚ_[p]))
  rw [hcoe, Padic.norm_p] at h
  rw [h]
  exact inv_lt_one_of_one_lt₀ (one_lt_p (p := p))

theorem norm_p_nonneg : (0 : ℝ) ≤ ‖(p : ℂ_[p])‖ := norm_nonneg _

variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

include hN hk hα in
/-- The centred estimate, in the form needed for the Riemann sums. -/
theorem exists_centred_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ), j ≤ k - 2 → ∀ (m : ℕ), 0 < m →
    ∀ b : ℕ, ‖Mom ιp f P α sg j m b - (b : ℂ_[p]) ^ j * Mom ιp f P α sg 0 m b‖
        ≤ C * ‖(p : ℂ_[p])‖ ^ m := by
  classical
  obtain ⟨C, hC0, hC⟩ := MTT.ordinary_centered_disk_bound hN hk ι ιp f P α hα
  refine ⟨C, hC0, fun j hj m hm b => ?_⟩
  set A : ℂ_[p] := (b : ℂ_[p]) with hA
  set Mc : ℕ → ℂ_[p] := fun t => ∑ u ∈ Finset.range (t + 1),
    (t.choose u : ℂ_[p]) * (-A) ^ (t - u) * Mom ιp f P α sg u m b with hMc
  have hcol : ∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ_[p]) * A ^ (j - t) * Mc t
      = Mom ιp f P α sg j m b := by
    have h := centered_collapse (R := ℂ_[p]) (fun u => Mom ιp f P α sg u m b) 1 (-A) j
    simp only [one_pow, one_mul, mul_one, neg_neg] at h
    simpa [hMc] using h
  have hMc0 : Mc 0 = Mom ιp f P α sg 0 m b := by simp [hMc]
  have hbound : ∀ t ∈ (Finset.range (j + 1)).erase 0,
      ‖(j.choose t : ℂ_[p]) * A ^ (j - t) * Mc t‖ ≤ C * ‖(p : ℂ_[p])‖ ^ m := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have htj : t ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_erase.mp ht).2)
    have hMct : ‖Mc t‖ ≤ C * ‖(p : ℂ_[p]) ^ (m * t)‖ := by
      have h := hC sg m hm (b : ℤ) t (le_trans htj hj)
      refine le_trans (le_of_eq ?_) h
      rw [hMc]
      refine congrArg _ (Finset.sum_congr rfl fun u _ => ?_)
      simp only [Mom, hA]
      push_cast
      ring
    calc ‖(j.choose t : ℂ_[p]) * A ^ (j - t) * Mc t‖
        = ‖(j.choose t : ℂ_[p])‖ * ‖A ^ (j - t)‖ * ‖Mc t‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * (C * ‖(p : ℂ_[p]) ^ (m * t)‖) := by
          refine mul_le_mul (mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
            (norm_nonneg _) zero_le_one) hMct (norm_nonneg _) (by positivity)
          rw [norm_pow, hA]
          exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)
      _ = C * ‖(p : ℂ_[p])‖ ^ (m * t) := by rw [norm_pow]; ring
      _ ≤ C * ‖(p : ℂ_[p])‖ ^ m := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          exact pow_le_pow_of_le_one (norm_nonneg _) norm_p_lt_one.le
            (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero ht0))
  have hsplit : ∑ t ∈ Finset.range (j + 1), (j.choose t : ℂ_[p]) * A ^ (j - t) * Mc t
      = (j.choose 0 : ℂ_[p]) * A ^ (j - 0) * Mc 0
        + ∑ t ∈ (Finset.range (j + 1)).erase 0,
            (j.choose t : ℂ_[p]) * A ^ (j - t) * Mc t :=
    (Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.succ_pos j))).symm
  rw [← hcol, hsplit, hMc0]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [add_sub_cancel_left]
  exact norm_sum_le_ultra (by positivity) _ _ hbound

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]
variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

include hN hk hα in
theorem MU_diskCM {j : ℕ} (hj : j ≤ k - 2) {n : ℕ} (hn : 0 < n) {a : ℤ}
    (ha : ¬ ((p : ℤ) ∣ a)) :
    MU ιp f P α sg (diskCM n ((a : ZMod (p ^ n))) j) = MTT.diskMoment f ιp P α sg j n a := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_centred_bound ιp f P α sg hN hk hα
  have hRS : ∀ m, n ≤ m → RS ιp f P α sg (diskCM n ((a : ZMod (p ^ n))) j) m
      = ∑ b ∈ Fib p n ((a : ZMod (p ^ n))) m, (b : ℂ_[p]) ^ j * Mom ιp f P α sg 0 m b := by
    intro m _
    rw [Fib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [mem_Idx] at hb
    have hval : diskCM n ((a : ZMod (p ^ n))) j (uNat b)
        = if ((b : ℕ) : ZMod (p ^ n)) = ((a : ZMod (p ^ n))) then (b : ℂ_[p]) ^ j else 0 := by
      simp only [diskCM, ContinuousMap.mul_apply, ContinuousMap.pow_apply, indCM, coordCM,
        ContinuousMap.coe_mk, toZModPow_uNat hb.2, coord_uNat hb.2]
      split <;> simp
    show diskCM n ((a : ZMod (p ^ n))) j (uNat b) * Mom ιp f P α sg 0 m b = _
    rw [hval]
    split <;> simp
  have hdiff : ∀ m, n ≤ m →
      ‖RS ιp f P α sg (diskCM n ((a : ZMod (p ^ n))) j) m
        - MTT.diskMoment f ιp P α sg j n a‖ ≤ C * ‖(p : ℂ_[p])‖ ^ m := by
    intro m hm
    rw [hRS m hm, ← sum_fiber ιp f P α sg hN hk hα hj hn ha m hm, ← Finset.sum_sub_distrib]
    refine norm_sum_le_ultra (by positivity) _ _ fun b _ => ?_
    rw [← norm_neg]
    have e : -((b : ℂ_[p]) ^ j * Mom ιp f P α sg 0 m b - Mom ιp f P α sg j m b)
        = Mom ιp f P α sg j m b - (b : ℂ_[p]) ^ j * Mom ιp f P α sg 0 m b := by ring
    rw [e]
    exact hC j hj m (by omega) b
  refine tendsto_nhds_unique (tendsto_RS ιp f P α sg hN hk hα _) ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, C * ‖(p : ℂ_[p])‖ ^ M₀ < ε := by
    obtain ⟨M₀, hM₁⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (C + 1) by positivity)
      (norm_p_lt_one (p := p))
    refine ⟨M₀, ?_⟩
    have h1 : C * ‖(p : ℂ_[p])‖ ^ M₀ ≤ C * (ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hM₁.le hC0
    have h2 : C * (ε / (C + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨max M₀ n, fun m hm => ?_⟩
  rw [ge_iff_le, Nat.max_le] at hm
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (le_trans (hdiff (m + 1) (by omega)) ?_) hM₀
  refine mul_le_mul_of_nonneg_left ?_ hC0
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_p_lt_one.le (by omega)

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

/-- Every unit lies in exactly one depth-`m` residue disk with index in `Idx p m`. -/
theorem exists_unique_idx {m : ℕ} (hm : 0 < m) (x : (ℤ_[p])ˣ) :
    ∃ b, b ∈ Idx p m ∧ ((b : ℕ) : ZMod (p ^ m)) = PadicInt.toZModPow m ((x : ℤ_[p]))
      ∧ ∀ b' ∈ Idx p m, ((b' : ℕ) : ZMod (p ^ m)) = PadicInt.toZModPow m ((x : ℤ_[p]))
          → b' = b := by
  classical
  set b : ℕ := (PadicInt.toZModPow m ((x : ℤ_[p]))).val with hb
  have hcast : ((b : ℕ) : ZMod (p ^ m)) = PadicInt.toZModPow m ((x : ℤ_[p])) := by
    rw [hb]
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hlt : b < p ^ m := ZMod.val_lt _
  have hp1 : (1 : ℝ) < (p : ℝ) := one_lt_p (p := p)
  have hsmall : ‖((x : ℤ_[p])) - ((b : ℤ_[p]))‖ < 1 := by
    have h1 : PadicInt.toZModPow m ((x : ℤ_[p])) = PadicInt.toZModPow m ((b : ℤ_[p])) := by
      rw [map_natCast, hcast]
    have h2 := norm_sub_le_of_toZModPow_eq h1
    refine lt_of_le_of_lt h2 ?_
    calc (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
          exact zpow_le_zpow_right₀ hp1.le (by omega)
      _ < 1 := by
          rw [zpow_neg, zpow_one]
          exact inv_lt_one_of_one_lt₀ hp1
  have hnd : ¬ (p ∣ b) := by
    intro hd
    have hbn : ‖((b : ℤ_[p]))‖ < 1 := by
      rw [show ((b : ℕ) : ℤ_[p]) = (((b : ℤ)) : ℤ_[p]) by push_cast; ring,
        PadicInt.norm_int_lt_one_iff_dvd]
      exact_mod_cast hd
    have hx1 : ‖((x : ℤ_[p]))‖ = 1 := PadicInt.norm_units x
    have : ‖((x : ℤ_[p]))‖ < 1 := by
      have e : ((x : ℤ_[p])) = ((b : ℤ_[p])) + (((x : ℤ_[p])) - ((b : ℤ_[p]))) := by ring
      rw [e]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hbn hsmall)
    rw [hx1] at this
    exact lt_irrefl _ this
  refine ⟨b, mem_Idx.mpr ⟨hlt, hnd⟩, hcast, fun b' hb' hb'2 => ?_⟩
  rw [mem_Idx] at hb'
  have := hb'2.trans hcast.symm
  have h3 : ((b' : ℕ) : ZMod (p ^ m)).val = ((b : ℕ) : ZMod (p ^ m)).val := by rw [this]
  rwa [ZMod.val_natCast_of_lt hb'.1, ZMod.val_natCast_of_lt hlt] at h3

end P2M

namespace P2M

variable {p : ℕ} [Fact p.Prime]

theorem coprime_of_not_dvd {b : ℕ} (h : ¬ (p ∣ b)) : IsCoprime ((b : ℤ)) ((p : ℤ)) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  simp only [Int.gcd_natCast_natCast]
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr h)

theorem not_dvd_of_coprime {a : ℤ} (h : IsCoprime a ((p : ℤ))) : ¬ ((p : ℤ) ∣ a) := by
  intro hd
  have hu := h.isUnit_of_dvd' hd dvd_rfl
  rw [Int.isUnit_iff] at hu
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  omega

/-- The locally constant approximation of `g` at depth `m`. -/
def stepFun (g : C((ℤ_[p])ˣ, ℂ_[p])) (m : ℕ) : C((ℤ_[p])ˣ, ℂ_[p]) :=
  ∑ b ∈ Idx p m, g (uNat b) • diskCM m (((b : ℕ)) : ZMod (p ^ m)) 0

theorem stepFun_apply (g : C((ℤ_[p])ˣ, ℂ_[p])) {m : ℕ} (hm : 0 < m) (x : (ℤ_[p])ˣ) :
    ∃ b, b ∈ Idx p m ∧ PadicInt.toZModPow m ((x : ℤ_[p])) = (((b : ℕ)) : ZMod (p ^ m))
      ∧ stepFun g m x = g (uNat b) := by
  classical
  obtain ⟨b, hb, hcast, huniq⟩ := exists_unique_idx hm x
  refine ⟨b, hb, hcast.symm, ?_⟩
  simp only [stepFun, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, diskCM, ContinuousMap.mul_apply, ContinuousMap.pow_apply, indCM, coordCM,
    ContinuousMap.coe_mk, pow_zero, mul_one]
  rw [Finset.sum_eq_single b]
  · rw [if_pos hcast.symm, mul_one]
  · intro b' hb' hne
    rw [if_neg, mul_zero]
    intro hcon
    exact hne (huniq b' hb' hcon.symm)
  · intro hcon
    exact absurd hb hcon

theorem stepFun_norm_le (g : C((ℤ_[p])ˣ, ℂ_[p])) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ u v : (ℤ_[p])ˣ,
      PadicInt.toZModPow m ((u : ℤ_[p])) = PadicInt.toZModPow m ((v : ℤ_[p])) →
        ‖g u - g v‖ ≤ ε) :
    ‖stepFun g m - g‖ ≤ ε := by
  refine (ContinuousMap.norm_le _ hε).mpr fun x => ?_
  obtain ⟨b, hb, hcast, hval⟩ := stepFun_apply g hm x
  rw [ContinuousMap.sub_apply, hval]
  refine hmod _ _ ?_
  rw [mem_Idx] at hb
  rw [toZModPow_uNat hb.2, hcast]

theorem tendsto_stepFun (g : C((ℤ_[p])ˣ, ℂ_[p])) :
    Filter.Tendsto (fun m => stepFun g (m + 1)) Filter.atTop (nhds g) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := exists_modulus (p := p) g (half_pos hε)
  refine ⟨n₀, fun m hm => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (stepFun_norm_le g (Nat.succ_pos m) (half_pos hε).le ?_) (by linarith)
  intro u v huv
  exact (hn₀ u v (modulus_mono (by omega) huv)).le

variable {N k : ℕ} {ι : MTT.Qbar →+* ℂ} (ιp : MTT.Qbar →+* ℂ_[p]) (f : MTT.Eigenform N k ι)
  (P : MTT.Periods k ι f.form) (α : ℂ_[p]) (sg : Bool)
variable (hN : 0 < N) (hk : 2 ≤ k) (hα : MTT.IsOrdinaryRoot f ιp α)

theorem measure_stepFun (ν : MTT.UnitMeasure p) (g : C((ℤ_[p])ˣ, ℂ_[p])) (m : ℕ)
    (hval : ∀ b ∈ Idx p m,
      ν (diskCM m (((b : ℕ)) : ZMod (p ^ m)) 0) = Mom ιp f P α sg 0 m b) :
    ν (stepFun g m) = RS ιp f P α sg g m := by
  rw [stepFun, map_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [map_smul, hval b hb]
  rfl

include hN hk hα in
theorem exists_measure : ∃ μ : MTT.UnitMeasure p, ∀ g, μ g = MU ιp f P α sg g := by
  obtain ⟨C, hC0, hM⟩ := exists_mass_bound ιp f P α sg hN hk hα
  let L : C((ℤ_[p])ˣ, ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] :=
    { toFun := MU ιp f P α sg
      map_add' := MU_add ιp f P α sg hN hk hα
      map_smul' := fun c g => MU_smul ιp f P α sg hN hk hα c g }
  exact ⟨L.mkContinuous C (fun g => MU_norm_le ιp f P α sg hN hk hα g hC0 hM), fun g => rfl⟩

include hN hk hα in
theorem measure_eq (ν : MTT.UnitMeasure p) (hν : MTT.RealizesMoments f ιp P α sg ν)
    (g : C((ℤ_[p])ˣ, ℂ_[p])) : ν g = MU ιp f P α sg g := by
  have hval : ∀ (m : ℕ), 0 < m → ∀ b ∈ Idx p m,
      ν (diskCM m (((b : ℕ)) : ZMod (p ^ m)) 0) = Mom ιp f P α sg 0 m b := by
    intro m hm b hb
    rw [mem_Idx] at hb
    obtain ⟨g', hg'1, hg'2⟩ := hν m hm ((b : ℕ) : ℤ) (coprime_of_not_dvd hb.2) 0 (Nat.zero_le _)
    have he : diskCM m (((b : ℕ)) : ZMod (p ^ m)) 0 = g' := by
      ext x
      rw [hg'1 x]
      have hc : (((b : ℕ)) : ZMod (p ^ m)) = ((((b : ℕ) : ℤ)) : ZMod (p ^ m)) := by
        push_cast; ring
      rw [hc]
      exact diskCM_apply m ((b : ℕ) : ℤ) 0 x
    rw [he, hg'2]
    rfl
  have h1 : Filter.Tendsto (fun m => ν (stepFun g (m + 1))) Filter.atTop (nhds (ν g)) :=
    ((map_continuous ν).tendsto g).comp (tendsto_stepFun g)
  have h2 : ∀ m : ℕ, ν (stepFun g (m + 1)) = RS ιp f P α sg g (m + 1) := fun m =>
    measure_stepFun ιp f P α sg ν g (m + 1) (hval (m + 1) (Nat.succ_pos m))
  refine tendsto_nhds_unique ?_ (tendsto_RS ιp f P α sg hN hk hα g)
  simpa only [h2] using h1

end P2M

open MTT in
theorem solution {p N k : ℕ} [Fact p.Prime] (hN : 0 < N) (hk : 2 ≤ k)
    (ι : Qbar →+* ℂ) (ιp : Qbar →+* ℂ_[p]) (f : Eigenform N k ι)
    (P : Periods k ι f.form) (α : ℂ_[p]) (hα : IsOrdinaryRoot f ιp α)
    (s : Bool) :
    ∃! μ : UnitMeasure p, RealizesMoments f ιp P α s μ := by
  obtain ⟨μ, hμ⟩ := P2M.exists_measure ιp f P α s hN hk hα
  refine ⟨μ, ?_, ?_⟩
  · intro n hn a ha j hj
    refine ⟨P2M.diskCM n ((a : ZMod (p ^ n))) j, fun x => P2M.diskCM_apply n a j x, ?_⟩
    rw [hμ]
    exact P2M.MU_diskCM ιp f P α s hN hk hα hj hn (P2M.not_dvd_of_coprime ha)
  · intro ν hν
    refine DFunLike.ext _ _ fun g => ?_
    rw [P2M.measure_eq ιp f P α s hN hk hα ν hν g, ← hμ g]
