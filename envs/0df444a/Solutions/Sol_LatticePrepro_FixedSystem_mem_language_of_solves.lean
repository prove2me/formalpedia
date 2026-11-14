-- Prove2me | solution 1 for LatticePrepro.FixedSystem.mem_language_of_solves
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:33:03.209796+00:00
-- url     : https://prove2.me/submissions/34fbf6a3-3a42-4af6-9742-4d76966cc483

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Theorems.Thm_LatticePrepro_FixedSystem_hammingNorm_eq_sum_tbl
import Theorems.Thm_LatticePrepro_FixedSystem_recover
import Theorems.Thm_LatticePrepro_FixedSystem_translation_pointwise
import Theorems.Thm_LatticePrepro_QuadraticVerifier_enc_assignOf
import Theorems.Thm_LatticePrepro_eq_zero_of_moment_eq_zero

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.FixedSystem end LatticePrepro.FixedSystem

namespace LatticePrepro

open Finsupp

section Moment

variable {F Ω : Type*} [CommRing F] [CommRing Ω] [Algebra F Ω]

/-- The moment map as an `F`-linear map. -/
noncomputable def momentₗ (k : ℕ) : (Ω →₀ F) →ₗ[F] Ω :=
  Finsupp.lsum F fun α => LinearMap.toSpanSingleton F Ω (α ^ k)

@[simp] lemma momentₗ_apply (f : Ω →₀ F) (k : ℕ) : momentₗ k f = moment f k := by
  simp only [momentₗ, moment, Finsupp.lsum_apply]
  rfl

lemma moment_eq_sum (f : Ω →₀ F) (k : ℕ) :
    moment f k = ∑ α ∈ f.support, f α • α ^ k := rfl

lemma moment_eq_sum_of_subset (f : Ω →₀ F) (k : ℕ) {s : Finset Ω} (hs : f.support ⊆ s) :
    moment f k = ∑ α ∈ s, f α • α ^ k := by
  rw [moment_eq_sum]
  exact Finset.sum_subset hs fun α _ hα => by
    simp [Finsupp.notMem_support_iff.mp hα]

lemma moment_sub (f g : Ω →₀ F) (k : ℕ) : moment (f - g) k = moment f k - moment g k := by
  simp only [← momentₗ_apply, map_sub]

lemma moment_smul (c : F) (f : Ω →₀ F) (k : ℕ) : moment (c • f) k = c • moment f k := by
  simp only [← momentₗ_apply, map_smul]

lemma moment_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Ω →₀ F) (k : ℕ) :
    moment (∑ i ∈ s, f i) k = ∑ i ∈ s, moment (f i) k := by
  simp only [← momentₗ_apply, map_sum]

/-- Extend the scalars of a coefficient function along `algebraMap F Ω`. -/
noncomputable def extendScalars (f : Ω →₀ F) : Ω →₀ Ω :=
  f.mapRange (algebraMap F Ω) (map_zero _)

@[simp] lemma extendScalars_apply (f : Ω →₀ F) (α : Ω) :
    extendScalars f α = algebraMap F Ω (f α) := rfl

lemma moment_extendScalars (f : Ω →₀ F) (k : ℕ) : moment (extendScalars f) k = moment f k := by
  unfold moment extendScalars
  rw [sum_mapRange_index (by simp)]
  simp [Algebra.smul_def]

@[simp] lemma extendScalars_zero : extendScalars (0 : Ω →₀ F) = 0 := by
  ext; simp

end Moment

end LatticePrepro

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

lemma assignOf_zero (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) : V.assignOf x u 0 = 1 := by
  simp [assignOf]

lemma assignOf_apply_of_le (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h0 : i.val ≠ 0) (hn : i.val ≤ V.n) :
    V.assignOf x u i = if x ⟨i.val - 1, by omega⟩ then 1 else 0 := by
  simp only [assignOf, h0, hn, ↓reduceDIte]

lemma assignOf_apply_of_eq (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : i.val = V.n + 1) : V.assignOf x u i = 1 := by
  simp [assignOf, h]

lemma assignOf_apply_of_lt (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) {i : Fin (V.S + 1)}
    (h : V.n + 1 < i.val) : V.assignOf x u i = u ⟨i, h⟩ := by
  have h0 : i.val ≠ 0 := by omega
  have hn : ¬ i.val ≤ V.n := by omega
  have hout : i.val ≠ V.n + 1 := by omega
  simp only [assignOf, h0, hn, hout, ↓reduceDIte]

lemma assignOf_inputIdx (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) (i : Fin V.n) :
    V.assignOf x u (V.inputIdx i) = if x i then 1 else 0 := by
  rw [V.assignOf_apply_of_le x u (i := V.inputIdx i) (by simp [inputIdx]) (by simp [inputIdx])]
  simp [inputIdx]

lemma assignOf_outputIdx (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    V.assignOf x u V.outputIdx = 1 :=
  V.assignOf_apply_of_eq x u rfl

lemma assignOf_aux (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) (i : V.AuxIdx) :
    V.assignOf x u i.1 = u i :=
  V.assignOf_apply_of_lt x u i.2

lemma assignOf_hasPrefix (x : Fin V.n → Bool) (u : V.AuxIdx → ZMod p) :
    V.HasPrefix x (V.assignOf x u) :=
  ⟨V.assignOf_inputIdx x u, V.assignOf_outputIdx x u⟩

end QuadraticVerifier

namespace EncodingTuple

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] {S : ℕ}
  (ε : EncodingTuple p K S)

lemma enc_sub (z z' : Fin (S + 1) → ZMod p) : ε.enc (z - z') = ε.enc z - ε.enc z' := by
  simp [enc, sub_smul, Finset.sum_sub_distrib]

/-- A vanishing combination `∑ c_i E_i = 0` with `c_0` arbitrary forces `c_i = 0` for `i ≥ 1`. -/
lemma eq_zero_of_sum_smul_eq_zero {c : Fin (S + 1) → ZMod p} (h : ∑ i, c i • ε.E i = 0)
    (i : Fin (S + 1)) (hi : i ≠ 0) : c i = 0 := by
  rw [Fin.sum_univ_succ, ε.E_zero, smul_zero, zero_add] at h
  obtain ⟨j, rfl⟩ : ∃ j : Fin S, i = j.succ := ⟨i.pred hi, (Fin.succ_pred i hi).symm⟩
  exact (Fintype.linearIndependent_iff.mp ε.linearIndependent) (fun j => c j.succ) h j

/-- Encodings are injective on assignments with equal constant coordinate. -/
lemma enc_injective {z z' : Fin (S + 1) → ZMod p} (h0 : z 0 = z' 0) (h : ε.enc z = ε.enc z') :
    z = z' := by
  funext i
  by_cases hi : i = 0
  · subst hi; exact h0
  · have : ∑ j, (z - z') j • ε.E j = 0 := by
      rw [← enc, enc_sub, h, sub_self]
    have := ε.eq_zero_of_sum_smul_eq_zero this i hi
    simpa [sub_eq_zero] using this

end EncodingTuple

end LatticePrepro

namespace LatticePrepro

namespace QuadraticVerifier

variable {p : ℕ} (V : QuadraticVerifier p)

lemma rep_comm (i j : Fin (V.S + 1)) : V.rep i j = V.rep j i := by
  unfold rep
  rcases lt_trichotomy i j with h | h | h
  · have h' : ¬ j < i := lt_asymm h
    simp [h, h']
  · subst h; rfl
  · have h' : ¬ i < j := lt_asymm h
    simp [h, h']

lemma rep_diag (i : Fin (V.S + 1)) : V.rep i i = V.rep i 0 := by
  unfold rep
  by_cases h0 : i = 0
  · subst h0; simp
  · have hpos : (0 : Fin (V.S + 1)) < i := Fin.pos_iff_ne_zero.mpr h0
    simp [h0, hpos]

end QuadraticVerifier

end LatticePrepro

namespace LatticePrepro

open Finsupp

section Aux

variable {Ω : Type} [Field Ω]

/-- Multiplication of a coefficient function by the variable: `α ↦ α · h α`. -/
noncomputable def mulVar (h : Ω →₀ Ω) : Ω →₀ Ω :=
  Finsupp.onFinset h.support (fun α => α * h α) fun α hα => by
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hα (by rw [h0, mul_zero])

@[simp] lemma mulVar_apply (h : Ω →₀ Ω) (α : Ω) : mulVar h α = α * h α := rfl

lemma support_mulVar_subset (h : Ω →₀ Ω) : (mulVar h).support ⊆ h.support :=
  Finsupp.support_onFinset_subset

lemma moment_mulVar (h : Ω →₀ Ω) (k : ℕ) : moment (mulVar h) k = moment h (k + 1) := by
  rw [moment_eq_sum_of_subset _ _ (support_mulVar_subset h), moment_eq_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [mulVar_apply, smul_eq_mul, smul_eq_mul, pow_succ]
  ring

end Aux

namespace FixedSystem

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)

lemma algebraMap_smul_eq (c : ZMod p) (y : K) :
    algebraMap K Ω (c • y) = c • algebraMap K Ω y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

open Classical in
/-- The union of the supports of the represented functions of all tables. -/
noncomputable def suppUnion (f : V.TblIdx → Ω →₀ ZMod p) : Finset Ω :=
  Finset.univ.biUnion fun T => (f T).support

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma mem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {T : V.TblIdx} {α : Ω} (h : f T α ≠ 0) :
    α ∈ suppUnion V f := by
  classical
  unfold suppUnion
  exact Finset.mem_biUnion.mpr ⟨T, Finset.mem_univ _, Finsupp.mem_support_iff.mpr h⟩

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma eq_zero_of_notMem_suppUnion {f : V.TblIdx → Ω →₀ ZMod p} {α : Ω}
    (h : α ∉ suppUnion V f) (T : V.TblIdx) : f T α = 0 :=
  by_contra fun h' => h (mem_suppUnion V h')

omit [Field Ω] [Algebra (ZMod p) Ω] in
lemma card_suppUnion_le (f : V.TblIdx → Ω →₀ ZMod p) :
    (suppUnion V f).card ≤ ∑ T, (f T).support.card := by
  classical
  unfold suppUnion
  exact Finset.card_biUnion_le

lemma hammingNorm_tbl_le (v : Col V R → ZMod p) (T : V.TblIdx) :
    hammingNorm (tbl V R v T) ≤ hammingNorm v := by
  rw [hammingNorm_eq_sum_tbl]
  exact Finset.single_le_sum (f := fun T => hammingNorm (tbl V R v T)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ T)

section Identities

variable {x : Fin V.n → Bool} {v : Col V R → ZMod p} (hv : Solves V R ε x v)
  (f : V.TblIdx → Ω →₀ ZMod p)
  (hf : ∀ T (k : R.Order), algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k)
  (hN : ∑ T, (f T).support.card < R.r)

include hv hf hN

/-- The encoding identity holds pointwise (paper, §4.4). -/
theorem encoding_pointwise (j : Fin (V.S + 1)) (α : Ω) :
    α * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 j)) α) =
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep i j)) α) := by
  set g : Ω →₀ Ω := mulVar (extendScalars (f (Sum.inl (V.rep 0 j)))) -
    ∑ i, algebraMap K Ω (ε.E i) • extendScalars (f (Sum.inl (V.rep i j))) with hg
  have hgapp : ∀ β, g β = β * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 j)) β) -
      ∑ i, algebraMap K Ω (ε.E i) * algebraMap (ZMod p) Ω (f (Sum.inl (V.rep i j)) β) := by
    intro β
    simp [hg, Algebra.smul_def]
  have hsupp : g.support ⊆ suppUnion V f := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβU
    apply hβ
    rw [hgapp]
    simp [eq_zero_of_notMem_suppUnion V hβU]
  have hmom : ∀ k < R.r, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (encLhs V R ε v j ⟨k, hk⟩) := by
      rw [encLhs, map_sub, map_sum, hg, moment_sub, moment_finset_sum, moment_mulVar,
        moment_extendScalars]
      unfold ptbl
      rw [hf _ (R.lowSucc ⟨k, hk⟩), MomentRepresentation.lowSucc_val]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [moment_smul, moment_extendScalars, smul_eq_mul, map_mul, hf _ (R.low ⟨k, hk⟩),
        MomentRepresentation.low_val]
    rw [this, hv.encoding j ⟨k, hk⟩, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans ((card_suppUnion_le V f).trans hN.le)) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact sub_eq_zero.mp h0

/-- The gate identities hold pointwise (paper, §4.4). -/
theorem gate_pointwise (b : Fin V.G) (α : Ω) :
    ∑ i, ∑ j, V.coeff b i j * f (Sum.inl (V.rep i j)) α = 0 := by
  set g : Ω →₀ Ω := ∑ i, ∑ j,
    algebraMap (ZMod p) Ω (V.coeff b i j) • extendScalars (f (Sum.inl (V.rep i j))) with hg
  have hgapp : ∀ β, g β =
      algebraMap (ZMod p) Ω (∑ i, ∑ j, V.coeff b i j * f (Sum.inl (V.rep i j)) β) := by
    intro β
    simp [hg, Algebra.smul_def]
  have hsupp : g.support ⊆ suppUnion V f := by
    intro β hβ
    rw [Finsupp.mem_support_iff] at hβ
    by_contra hβU
    apply hβ
    rw [hgapp]
    simp [eq_zero_of_notMem_suppUnion V hβU]
  have hmom : ∀ k < R.r, moment g k = 0 := by
    intro k hk
    have : moment g k = algebraMap K Ω (gateLhs V R v b ⟨k, hk⟩) := by
      rw [gateLhs, map_sum, hg, moment_finset_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, moment_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [moment_smul, moment_extendScalars, smul_eq_mul, algebraMap_smul_eq, Algebra.smul_def]
      unfold ptbl
      rw [hf _ (R.low ⟨k, hk⟩), MomentRepresentation.low_val]
    rw [this, hv.gate b ⟨k, hk⟩, map_zero]
  have hg0 : g = 0 := eq_zero_of_moment_eq_zero g
    ((Finset.card_le_card hsupp).trans ((card_suppUnion_le V f).trans hN.le)) hmom
  have h0 : g α = 0 := by rw [hg0]; rfl
  rw [hgapp] at h0
  exact (map_eq_zero_iff _ (algebraMap (ZMod p) Ω).injective).mp h0

end Identities

/-- **Soundness, weight form** (Theorem 4.6): a solution of weight below the threshold `r · D / 2`
certifies membership in the language. -/
private theorem mem_language_of_solves {x : Fin V.n → Bool} {v : Col V R → ZMod p}
    (hv : Solves V R ε x v) (hw : 2 * hammingNorm v < R.r * R.numBlocks) : x ∈ V.Language := by
  classical
  -- (1) represented functions
  have htbl : ∀ T, 2 * hammingNorm (tbl V R v T) < R.r * R.numBlocks := fun T =>
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (hammingNorm_tbl_le V R v T)) hw
  choose f hf using fun T => R.sound (tbl V R v T) (hv.constraint T) (htbl T)
  have hf' : ∀ T (k : R.Order),
      algebraMap K Ω (R.momentMap k (tbl V R v T)) = moment (f T) k := fun T => (hf T).1
  have hN : ∑ T, (f T).support.card < R.r := by
    have h1 : R.numBlocks * ∑ T, (f T).support.card ≤ 2 * hammingNorm v := by
      rw [Finset.mul_sum, hammingNorm_eq_sum_tbl, Finset.mul_sum]
      exact Finset.sum_le_sum fun T _ => (hf T).2
    have h2 : R.numBlocks * ∑ T, (f T).support.card < R.numBlocks * R.r :=
      calc _ ≤ 2 * hammingNorm v := h1
        _ < R.r * R.numBlocks := hw
        _ = R.numBlocks * R.r := mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_left h2
  -- (5) the coset sum
  set θ : Ω := algebraMap K Ω (V.instanceEnc ε x) with hθ
  set c : V.AuxIdx → Ω := fun i => algebraMap K Ω (ε.E i.1) with hc
  let pt : (V.AuxIdx → ZMod p) → Ω := fun u => algebraMap K Ω (ε.enc (V.assignOf x u))
  have hpt : ∀ u, pt u = θ + ∑ i, u i • c i := by
    intro u
    simp only [pt, V.enc_assignOf ε x u, map_add, map_sum, algebraMap_smul_eq, hθ, hc]
  have hpt0 : pt 0 = θ := by
    simp only [pt]
    rfl
  have hpt_sub : ∀ u (i : V.AuxIdx), pt (u - Pi.single i 1) = pt u - c i := by
    intro u i
    rw [hpt, hpt]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul,
      zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hpt_eq : ∀ u, pt u = θ ↔ u = 0 := by
    intro u
    constructor
    · intro h
      have h1 : ε.enc (V.assignOf x u) = ε.enc (V.assignOf x 0) :=
        (algebraMap K Ω).injective (by rw [← hpt0] at h; exact h)
      have h2 : V.assignOf x u = V.assignOf x 0 :=
        ε.enc_injective (by rw [V.assignOf_zero, V.assignOf_zero]) h1
      funext i
      have := congrFun h2 i.1
      rw [V.assignOf_aux, V.assignOf_aux] at this
      exact this
    · rintro rfl; exact hpt0
  -- sum the pointwise translation identity over the coset
  have hT : ∀ u, algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) (pt u)) -
      ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u - c i)) -
        algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u))) -
      Finsupp.single θ (1 : Ω) (pt u) = 0 :=
    fun u => translation_pointwise V R ε hv f hf' hN (pt u)
  have hsum0 := Finset.sum_eq_zero (s := Finset.univ) fun u _ => hT u
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum0
  have hmid : ∑ u, ∑ i : V.AuxIdx, (algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u - c i)) -
      algebraMap (ZMod p) Ω (f (Sum.inr i) (pt u))) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.subRight (Pi.single i 1)) _ _ fun u => by
      simp [hpt_sub]
  have hlast : ∑ u, Finsupp.single θ (1 : Ω) (pt u) = 1 := by
    rw [Finset.sum_eq_single (0 : V.AuxIdx → ZMod p)]
    · rw [hpt0, Finsupp.single_eq_same]
    · intro u _ hu
      have : pt u ≠ θ := fun h => hu ((hpt_eq u).mp h)
      rw [Finsupp.single_apply, if_neg (Ne.symm this)]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hmid, hlast, sub_zero, sub_eq_zero] at hsum0
  obtain ⟨u, hu⟩ : ∃ u, f (Sum.inl (V.rep 0 0)) (pt u) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : ∑ u, algebraMap (ZMod p) Ω (f (Sum.inl (V.rep 0 0)) (pt u)) = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [h u, map_zero]
    rw [this] at hsum0
    exact zero_ne_one hsum0
  -- (4) recover an accepting computation at the support point
  obtain ⟨z, hzb, hzv, hzenc⟩ := recover V ε (Fv := fun i j => f (Sum.inl (V.rep i j)) (pt u))
    (fun i j => by rw [V.rep_comm]) (fun i => by rw [V.rep_diag])
    (fun j => encoding_pointwise V R ε hv f hf' hN j (pt u))
    (fun b => gate_pointwise V R ε hv f hf' hN b (pt u)) hu
  have hz : z = V.assignOf x u := by
    apply ε.enc_injective (by rw [hzb.1, V.assignOf_zero])
    exact (algebraMap K Ω).injective hzenc
  exact ⟨z, hzb, hzv, hz ▸ V.assignOf_hasPrefix x u⟩

end FixedSystem

end LatticePrepro

open LatticePrepro
open Finsupp
open LatticePrepro.FixedSystem
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    {Ω : Type} [Field Ω] [Algebra (ZMod p) Ω] [Algebra K Ω] [IsScalarTower (ZMod p) K Ω]
    (V : QuadraticVerifier p) (R : MomentRepresentation p K Ω) (ε : EncodingTuple p K V.S)
theorem solution {x : Fin V.n → Bool} {v : Col V R → ZMod p}
    (hv : Solves V R ε x v) (hw : 2 * hammingNorm v < R.r * R.numBlocks) : x ∈ V.Language :=
  @LatticePrepro.FixedSystem.mem_language_of_solves p _ K _ _ Ω _ _ _ _ V R ε x v hv hw
