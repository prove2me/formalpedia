-- Prove2me | solution 1 for GenericGroupWE.Main.prop_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T15:35:45.182253+00:00
-- url     : https://prove2.me/submissions/ffba0f55-dec0-42e1-bd77-ecfbf8d5e9ba

import Mathlib
import Definitions.Def_GenericGroupWE_Main_Scheme

set_option maxHeartbeats 2000000

-- Exact source with hygienic private names: WitnessEncryption.Runtime.Binary.Value

namespace WitnessEncryption.Runtime.Binary

/-- Denotation only: executable arithmetic traverses the bit lists themselves. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : List Bool) :
    value (b :: bs) = (if b then 1 else 0) + 2 * value bs := rfl

theorem value_eq_foldr (bs : List Bool) : value bs = bs.foldr Nat.bit 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [value, ih, Nat.bit, Nat.add_comm]

@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h, value_cons, ih]
    cases b <;> simp [Nat.bit, Nat.add_comm]

theorem value_lt_two_pow_length (bs : List Bool) : value bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih => cases b <;> simp only [value_cons, List.length_cons, pow_succ] <;>
      norm_num at * <;> omega

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append, value_cons, List.length_cons, pow_succ, ih]; ring

@[simp] theorem value_replicate_false (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n <;> simp [List.replicate_succ, *]

/-- Truncating after a known sufficient binary width preserves denotation. -/
theorem value_take_of_lt (bs : List Bool) (w : ℕ) (h : value bs < 2 ^ w) :
    value (bs.take w) = value bs := by
  induction w generalizing bs with
  | zero => simp only [pow_zero] at h; simp; omega
  | succ w ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      have ht : value bs < 2 ^ w := by
        simp only [value_cons, pow_succ] at h
        split at h <;> omega
      simp only [List.take_succ_cons, value_cons, ih bs ht]

end WitnessEncryption.Runtime.Binary

namespace GenericGroupWE.Main.SamplingRuntime
theorem packet_length (bs : Bits) : (packet bs).length = 2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [packet,List.length_cons,ih]; omega

theorem unpacket_packet_append (bs tail : Bits) :
    unpacket (packet bs ++ tail) = some (bs,tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [packet,unpacket,ih]

theorem unpacket_packet (bs : Bits) : unpacket (packet bs) = some (bs,[]) := by
  simpa using unpacket_packet_append bs []


end GenericGroupWE.Main.SamplingRuntime

namespace GenericGroupWE.Main.SamplingRuntime
private theorem word_nat_lt (bs : Bits) : bitsNat bs < 2^bs.length := by
  induction bs with
  | nil => simp [bitsNat]
  | cons b bs ih =>
    cases b <;> simp only [bitsNat,List.foldr_cons,Nat.bit_false,Nat.bit_true,List.length_cons,pow_succ] at * <;> omega

private theorem word_nat_injective (xs ys : Bits) (hlen : xs.length = ys.length)
    (hval : bitsNat xs = bitsNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      have hb : b = c := by
        simpa only [bitsNat,List.foldr_cons,Nat.bodd_bit] using congrArg Nat.bodd hval
      have ht : bitsNat xs = bitsNat ys := by
        simpa only [bitsNat,List.foldr_cons,Nat.div2_bit] using congrArg Nat.div2 hval
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      rw [hb,ih ys hlen ht]

/-- Mathematical finite value map only; it is never executed by the controller. -/
def wordValue (n : ℕ) (f : Fin n → Bool) : Fin (2^n) :=
  ⟨bitsNat (List.ofFn f), by simpa using word_nat_lt (List.ofFn f)⟩

theorem wordValue_bijective (n : ℕ) : Function.Bijective (wordValue n) := by
  have hi : Function.Injective (wordValue n) := by
    intro f g h
    apply List.ofFn_injective
    apply word_nat_injective
    · simp
    · exact congrArg Fin.val h
  have e : (Fin n → Bool) ≃ Fin (2^n) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_fun])
  exact ⟨hi,hi.surjective_of_finite e⟩

/-- Fixed-width exposure is a left inverse on every bit word, including zero padding. -/
theorem fixedBits_word_nat (bs : Bits) : fixedBits bs.length (bitsNat bs) = bs := by
  induction bs with
  | nil => simp [fixedBits]
  | cons b bs ih =>
    simp only [List.length_cons,bitsNat,List.foldr_cons,fixedBits,List.ofFn_succ,Fin.val_zero,Fin.val_succ,
      Nat.testBit_bit_zero,Nat.testBit_bit_succ]
    exact congrArg (List.cons b) ih

/-- Canonical fixedBits/bitsNat inverse on the exact finite range. -/
theorem word_nat_fixedBits (width n : ℕ) (hn : n < 2^width) :
    bitsNat (fixedBits width n) = n := by
  obtain ⟨f,hf⟩ := (wordValue_bijective width).2 ⟨n,hn⟩
  have hv : bitsNat (List.ofFn f) = n := congrArg Fin.val hf
  have hi := fixedBits_word_nat (List.ofFn f)
  simp only [List.length_ofFn,hv] at hi
  rw [hi,hv]


end GenericGroupWE.Main.SamplingRuntime

namespace GenericGroupWE.Main.SamplingRuntime
/-- Interpreter context, used only in semantic statements. The transition never constructs this. -/
def encodingContext (p : PrimeOrder) (σ : Encoding p.val) : GroupContext :=
  ⟨p.val,p.property,σ⟩

theorem fixedBits_injective (width : ℕ) {x y : ℕ} (hx : x < 2^width) (hy : y < 2^width)
    (h : fixedBits width x = fixedBits width y) : x = y := by
  have := congrArg bitsNat h
  rwa [word_nat_fixedBits width x hx,word_nat_fixedBits width y hy] at this

theorem exposed_label_injective (p : ℕ) (σ : Encoding p) : Function.Injective (label σ) := by
  intro a b hab
  apply σ.injective
  apply Fin.ext
  exact fixedBits_injective (labelLength p) (σ a).isLt (σ b).isLt hab

/-- Every valid exposed label decodes to precisely its original field index. -/
theorem decode_exposed_label (Γ : GroupContext) (a : Fin Γ.p) : Γ.decode (label Γ.σ a) = some a := by
  unfold GroupContext.decode
  rw [List.finRange,List.find?_ofFn_eq_some]
  refine ⟨by simp, a, rfl, ?_⟩
  intro b hba hlabel
  have h := exposed_label_injective Γ.p Γ.σ (eq_of_beq hlabel)
  exact (ne_of_lt hba) h

/-- The two query modes agree exactly with finite modular addition/subtraction. -/
theorem query_exposed_label (Γ : GroupContext) (subtract : Bool) (a b : Fin Γ.p) :
    Γ.query subtract (label Γ.σ a) (label Γ.σ b) =
      some (label Γ.σ ⟨(if subtract then a.val+Γ.p-b.val else a.val+b.val) % Γ.p,
        Nat.mod_lt _ Γ.prime.pos⟩) := by
  simp [GroupContext.query,decode_exposed_label]

theorem query_encodeField (p : PrimeOrder) (σ : Encoding p.val) (subtract : Bool)
    (a b : ZMod p.val) :
    (encodingContext p σ).query subtract (encodeField σ a) (encodeField σ b) =
      some (encodeField σ (if subtract then a-b else a+b)) := by
  change (encodingContext p σ).query subtract
    (label σ ⟨a.val,ZMod.val_lt a⟩) (label σ ⟨b.val,ZMod.val_lt b⟩) = _
  have hq := query_exposed_label (encodingContext p σ) subtract ⟨a.val,ZMod.val_lt a⟩ ⟨b.val,ZMod.val_lt b⟩
  dsimp only [encodingContext] at hq ⊢
  rw [hq]
  apply congrArg some
  apply congrArg (label σ)
  apply Fin.ext
  cases subtract with
  | false => exact (ZMod.val_add a b).symm
  | true =>
    have hle : b.val ≤ a.val+p.val := (ZMod.val_lt b).le.trans (Nat.le_add_left _ _)
    have hc : ((a.val+p.val-b.val : ℕ) : ZMod p.val) = a-b := by
      rw [Nat.cast_sub hle,Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self,
        ZMod.natCast_zmod_val,add_zero]
    have hv := congrArg ZMod.val hc
    simpa only [ZMod.val_natCast,↓reduceIte] using hv


end GenericGroupWE.Main.SamplingRuntime

-- Exact source with hygienic private names: WitnessEncryption.HonestDecryption

namespace GenericGroupWE.Main
open scoped BigOperators
open SamplingRuntime

namespace CorrectnessProof

lemma bitsNat_bits (n : ℕ) : bitsNat n.bits = n := by
  rw [bitsNat, ← WitnessEncryption.Runtime.Binary.value_eq_foldr,
    WitnessEncryption.Runtime.Binary.value_bits]

lemma generator_encode (p : PrimeOrder) (σ : Encoding p.val) :
    (encodingContext p σ).generator = encodeField σ (1 : ZMod p.val) := by
  simp [encodingContext, GroupContext.generator, encodeField]
  apply congrArg (label σ)
  apply Fin.ext
  simp [ZMod.val_one, Nat.mod_eq_of_lt p.property.one_lt]

lemma scalar_fold_encode (p : PrimeOrder) (σ : Encoding p.val) (base : ZMod p.val)
    (bits : Bits) :
    bits.foldr (fun bit acc => do
      let acc ← acc
      let doubled ← (encodingContext p σ).query false acc acc
      if bit then (encodingContext p σ).query false doubled (encodeField σ base) else pure doubled)
      (some (encodeField σ 0)) =
        some (encodeField σ ((bitsNat bits : ZMod p.val)*base)) := by
  induction bits with
  | nil => simp [bitsNat]
  | cons bit bits ih =>
    rw [List.foldr_cons, ih]
    cases bit <;> simp [query_encodeField, bitsNat, List.foldr_cons, Nat.bit]
    <;> congr 2 <;> push_cast <;> ring

lemma scalarHandle_encode (p : PrimeOrder) (σ : Encoding p.val) (base : ZMod p.val)
    (n : ℕ) :
    scalarHandle (encodingContext p σ) (encodeField σ 0) (encodeField σ base) n =
      some (encodeField σ ((n : ZMod p.val)*base)) := by
  unfold scalarHandle
  rw [scalar_fold_encode, bitsNat_bits]

lemma schemeHandles_pack (g xs ys : Bits) :
    schemeHandles (pack [g,xs,ys]) = some (g,xs,ys) := by
  simp [schemeHandles, pack, unpacket_packet_append, unpacket_packet]

lemma unpackHandles_pack (xs : List Bits) :
    unpackHandles xs.length (pack xs) = some xs := by
  induction xs with
  | nil => simp [unpackHandles, pack]
  | cons x xs ih =>
    simp only [List.length_cons, pack, List.map_cons, List.flatten_cons,
      unpackHandles, unpacket_packet_append]
    change ((unpackHandles xs.length (pack xs)).bind fun a => some (x :: a)) = _
    rw [ih]
    rfl

lemma linear_fold_encode (p : PrimeOrder) (σ : Encoding p.val)
    (pairs : List (ℕ × ZMod p.val)) (acc : ZMod p.val) :
    (pairs.map (fun q => (q.1,encodeField σ q.2))).foldl (fun acc term => do
      let acc ← acc
      let term ← scalarHandle (encodingContext p σ) (encodeField σ 0) term.2 term.1
      (encodingContext p σ).query false acc term) (some (encodeField σ acc)) =
      some (encodeField σ (acc + (pairs.map (fun q => (q.1 : ZMod p.val)*q.2)).sum)) := by
  induction pairs generalizing acc with
  | nil => simp
  | cons pair pairs ih =>
    simp only [List.map_cons, List.foldl_cons, Option.bind_eq_bind, Option.bind_some, scalarHandle_encode,
      query_encodeField, Bool.false_eq_true, ↓reduceIte]
    simpa only [Option.bind_eq_bind, List.sum_cons, add_assoc] using
      ih (acc + (pair.1 : ZMod p.val)*pair.2)

lemma linearHandle_pairs (p : PrimeOrder) (σ : Encoding p.val)
    (pairs : List (ℕ × ZMod p.val)) :
    linearHandle (encodingContext p σ) (pairs.map Prod.fst) (pairs.map (fun q => encodeField σ q.2)) =
      some (encodeField σ ((pairs.map (fun q => (q.1 : ZMod p.val)*q.2)).sum)) := by
  have hz : (pairs.map Prod.fst).zip (pairs.map (fun q => encodeField σ q.2)) =
      pairs.map (fun q => (q.1,encodeField σ q.2)) := by
    induction pairs <;> simp_all
  unfold linearHandle
  rw [generator_encode, query_encodeField]
  simp only [↓reduceIte, sub_self, Option.bind_eq_bind, Option.bind_some, hz]
  simpa only [Option.bind_eq_bind, zero_add] using linear_fold_encode p σ pairs 0

lemma linearHandle_encode (p : PrimeOrder) (σ : Encoding p.val) (n : ℕ)
    (a x : Fin n → ZMod p.val) :
    linearHandle (encodingContext p σ) (List.ofFn fun i => (a i).val)
      (List.ofFn fun i => encodeField σ (x i)) =
        some (encodeField σ (∑ i, a i*x i)) := by
  have h := linearHandle_pairs p σ (List.ofFn fun i => ((a i).val,x i))
  simpa only [List.map_ofFn, Function.comp_def, ZMod.natCast_zmod_val, List.sum_ofFn] using h


lemma multipleHandles_encode (p : PrimeOrder) (σ : Encoding p.val) (H : ZMod p.val) (n : ℕ) :
    multipleHandles (encodingContext p σ) (encodeField σ H) n =
      some ((List.range n).map (fun i => encodeField σ (((i+1 : ℕ) : ZMod p.val)*H))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multipleHandles, ih]
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.getLast?_map, List.getLast?_range, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel_right, Option.map_some, Option.bind_eq_bind, Option.bind_some]
      rw [query_encodeField]
      simp only [↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def, List.range_succ, List.map_append,
        List.map_singleton]
      congr 3
      push_cast
      ring

lemma encode_injective (p : PrimeOrder) (σ : Encoding p.val) :
    Function.Injective (encodeField σ : ZMod p.val → Bits) := by
  intro x y h
  have hh := exposed_label_injective p.val σ h
  have hv := congrArg Fin.val hh
  exact ZMod.val_injective p.val hv

lemma multiple_list_contains (p : PrimeOrder) (σ : Encoding p.val) (H Z : ZMod p.val) (n : ℕ) :
    (((List.range n).map (fun i => encodeField σ (((i+1 : ℕ) : ZMod p.val)*H))).contains
      (encodeField σ Z)) = decide (∃ q : Fin n, Z = ((q.val+1 : ℕ) : ZMod p.val)*H) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,he⟩
    exact ⟨⟨i,hi⟩, ((encode_injective p σ) he).symm⟩
  · rintro ⟨q,hq⟩
    exact ⟨q.val,q.isLt, congrArg (encodeField σ) hq.symm⟩


end CorrectnessProof

theorem honest_decryption_identity :
    ∀ (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p) (w : RankOneCertificate B)
      (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
      (t : Fin B.k → ZMod p.val) (message : Bool),
      schemeDecryption w (coordinateCiphertext B σ s r t message) =
        some (decide (¬ ∃ q : Fin (m*m),
          (∑ j, w.coefficients j * (if message then t j else
            ∑ i : Fin m, ∑ l : Fin m, s i * B.matrices j i l * (r l : ZMod p.val))) =
            ((q.val+1 : ℕ) : ZMod p.val) * (∑ i, w.left i*s i))) := by
  intro m p B w σ s r t message
  classical
  let y : Fin B.k → ZMod p.val := fun j => if message then t j else
    ∑ i : Fin m, ∑ l : Fin m, s i * B.matrices j i l * (r l : ZMod p.val)
  have hX : unpackHandles m (pack (List.ofFn fun i => encodeField σ (s i))) =
      some (List.ofFn fun i => encodeField σ (s i)) := by
    simpa only [List.length_ofFn] using CorrectnessProof.unpackHandles_pack
      (List.ofFn fun i => encodeField σ (s i))
  have hY : unpackHandles B.k (pack (List.ofFn fun j => encodeField σ (y j))) =
      some (List.ofFn fun j => encodeField σ (y j)) := by
    simpa only [List.length_ofFn] using CorrectnessProof.unpackHandles_pack
      (List.ofFn fun j => encodeField σ (y j))
  change schemeDecryption w
    ⟨some (encodingContext p σ), some (pack [(encodingContext p σ).generator,
      pack (List.ofFn fun i => encodeField σ (s i)), pack (List.ofFn fun j => encodeField σ (y j))])⟩ = _
  unfold schemeDecryption
  simp only [Option.bind_eq_bind, Option.bind_some,
    show (encodingContext p σ).p = p.val from rfl, ne_eq, not_true_eq_false, ↓reduceIte,
    CorrectnessProof.schemeHandles_pack, hX, hY, CorrectnessProof.linearHandle_encode,
    CorrectnessProof.multipleHandles_encode, CorrectnessProof.multiple_list_contains,
    Option.pure_def, decide_not]
  rfl

end GenericGroupWE.Main


-- Exact source with hygienic private names: WitnessEncryption.BoundedUniform

open scoped BigOperators ENNReal

namespace GenericGroupWE.Main

private theorem BoundedUniform__bounded_uniform_step (D a : ℕ) (hD : 0 < D) (y : Option ℕ) :
    boundedUniform D (a+1) y =
      (∑ i ∈ Finset.range D, ((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * (PMF.pure (some i) : PMF (Option ℕ)) y) +
      ((2 ^ Nat.clog 2 D - D : ℕ) : ℝ≥0∞) *
        (((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * boundedUniform D a y) := by
  classical
  let M := 2 ^ Nat.clog 2 D
  have hDM : D ≤ M := Nat.le_pow_clog (by decide) D
  rw [boundedUniform, PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  change (∑ i : Fin M, (M : ℝ≥0∞)⁻¹ *
    (if i.val < D then PMF.pure (some i.val) else boundedUniform D a) y) = _
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (M : ℝ≥0∞)⁻¹ *
    (if i < D then PMF.pure (some i) else boundedUniform D a) y)]
  rw [show M = D + (M-D) from (Nat.add_sub_of_le hDM).symm, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
    simp only [Nat.add_sub_of_le hDM]
    rfl
  · simp only [show ∀ i : ℕ, ¬D+i<D by omega, if_false, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.add_sub_of_le hDM]
    rfl

private theorem BoundedUniform__bounded_uniform_failure_step (D a : ℕ) (hD : 0 < D) :
    boundedUniform D (a+1) none =
      ((2 ^ Nat.clog 2 D - D : ℕ) : ℝ≥0∞) *
        (((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * boundedUniform D a none) := by
  rw [BoundedUniform__bounded_uniform_step D a hD]
  simp

private theorem BoundedUniform__bounded_uniform_success_step (D a x : ℕ) (hD : 0 < D) :
    boundedUniform D (a+1) (some x) =
      (if x < D then ((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ else 0) +
      ((2 ^ Nat.clog 2 D - D : ℕ) : ℝ≥0∞) *
        (((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * boundedUniform D a (some x)) := by
  classical
  rw [BoundedUniform__bounded_uniform_step D a hD]
  simp [PMF.pure_apply, mul_ite]

private theorem BoundedUniform__bounded_uniform_real_law (D : ℕ) (hD : 0 < D) :
    ∀ a : ℕ,
      (boundedUniform D a none).toReal ≤ (1 / 2 : ℝ)^a ∧
      ∀ x : ℕ, (boundedUniform D a (some x)).toReal * D =
        if x < D then 1 - (boundedUniform D a none).toReal else 0 := by
  let M := 2 ^ Nat.clog 2 D
  have hDM : D ≤ M := Nat.le_pow_clog (by decide) D
  have hMpos : 0 < M := pow_pos (by decide) _
  have hMtwo : M ≤ 2*D := by
    by_cases h : D = 1
    · simp [M, h]
    have hlarge : 1 < D := by omega
    have hc : 0 < Nat.clog 2 D := Nat.clog_pos (by decide) hlarge
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hlarge
    rw [Nat.pred_eq_sub_one] at hp
    have he : M = 2 ^ (Nat.clog 2 D - 1) * 2 := by
      dsimp [M]
      rw [← pow_succ]
      congr 1
      omega
    omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDMr : (D : ℝ) ≤ M := by exact_mod_cast hDM
  have hMtwor : (M : ℝ) ≤ 2*D := by exact_mod_cast hMtwo
  let q : ℝ := (M - D : ℕ) * (M : ℝ)⁻¹
  have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1/2 := by
    dsimp [q]
    rw [Nat.cast_sub hDM, ← div_eq_mul_inv]
    apply (div_le_iff₀ hMr).2
    linarith
  have hqsum : (M : ℝ)⁻¹ * D + q = 1 := by
    dsimp [q]
    rw [Nat.cast_sub hDM]
    field_simp [ne_of_gt hMr] <;> ring
  have hf (a : ℕ) : (boundedUniform D (a+1) none).toReal =
      q * (boundedUniform D a none).toReal := by
    rw [BoundedUniform__bounded_uniform_failure_step D a hD]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    dsimp [q, M]
    ring
  have hs (a x : ℕ) : (boundedUniform D (a+1) (some x)).toReal =
      (if x < D then (M : ℝ)⁻¹ else 0) +
        q * (boundedUniform D a (some x)).toReal := by
    have hn := (boundedUniform D (a+1)).apply_ne_top (some x)
    rw [BoundedUniform__bounded_uniform_success_step D a x hD] at hn ⊢
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp hn).1 (ENNReal.add_ne_top.mp hn).2]
    by_cases hx : x < D <;>
      simp only [hx, ↓reduceIte, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_zero] <;>
      dsimp [q, M] <;> ring
  intro a
  induction a with
  | zero =>
    change ((PMF.pure (none : Option ℕ)) none).toReal ≤ (1/2 : ℝ)^0 ∧
      ∀ x : ℕ, ((PMF.pure (none : Option ℕ)) (some x)).toReal * D =
        if x < D then 1 - ((PMF.pure (none : Option ℕ)) none).toReal else 0
    simp
  | succ a ih =>
    constructor
    · rw [hf, pow_succ]
      simpa only [mul_comm] using
        (mul_le_mul hqhalf ih.1 (ENNReal.toReal_nonneg) (by positivity))
    · intro x
      rw [hs, hf]
      have hi := ih.2 x
      by_cases hx : x < D
      · simp only [hx, ↓reduceIte] at hi ⊢
        calc
          ((M : ℝ)⁻¹ + q * (boundedUniform D a (some x)).toReal) * D =
              (M : ℝ)⁻¹ * D + q * ((boundedUniform D a (some x)).toReal * D) := by ring
          _ = (M : ℝ)⁻¹ * D + q * (1 - (boundedUniform D a none).toReal) := by rw [hi]
          _ = 1 - q * (boundedUniform D a none).toReal := by nlinarith [hqsum]
      · simp only [hx, ↓reduceIte, zero_add] at hi ⊢
        rw [mul_assoc, hi, mul_zero]

/-- Rejection-sampling failure and exact uniformity on success. -/
theorem bounded_uniform_law :
    ∀ (D attempts : ℕ), 0 < D →
  (boundedUniform D attempts) none ≤ (2 : ℝ≥0∞)⁻¹ ^ attempts ∧
  ∀ x : ℕ,
    (boundedUniform D attempts) (some x) * (D : ℝ≥0∞) =
      if x < D then 1 - (boundedUniform D attempts) none else 0 := by
  intro D a hD
  obtain ⟨hf, hs⟩ := BoundedUniform__bounded_uniform_real_law D hD a
  constructor
  · apply (ENNReal.toReal_le_toReal ((boundedUniform D a).apply_ne_top none) (by finiteness)).mp
    simpa using hf
  · intro x
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.mul_ne_top ((boundedUniform D a).apply_ne_top (some x)) (by simp))
      (by split_ifs <;> finiteness)).mp
    have hi := hs x
    by_cases hx : x < D
    · simp only [hx, ↓reduceIte] at hi ⊢
      rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_sub_of_le ((boundedUniform D a).coe_le_one none) (by finiteness)]
      simpa using hi
    · simp only [hx, ↓reduceIte] at hi ⊢
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_zero] using hi

end GenericGroupWE.Main


-- Exact source with hygienic private names: WitnessEncryption.BoundedCoordinates

open scoped ENNReal BigOperators
namespace GenericGroupWE.Main

private def BoundedCoordinates__optionCons (a : Option ℕ) (xs : Option (List ℕ)) : Option (List ℕ) := do
  let a ← a
  let xs ← xs
  pure (a :: xs)

private theorem BoundedCoordinates__optionCons_none (a : Option ℕ) (xs : Option (List ℕ)) :
    none = BoundedCoordinates__optionCons a xs ↔ a = none ∨ xs = none := by
  cases a <;> cases xs <;> simp [BoundedCoordinates__optionCons]

private theorem BoundedCoordinates__optionCons_some (a : Option ℕ) (ys : Option (List ℕ)) (x : ℕ) (xs : List ℕ) :
    some (x :: xs) = BoundedCoordinates__optionCons a ys ↔ a = some x ∧ ys = some xs := by
  cases a <;> cases ys <;> simp [BoundedCoordinates__optionCons, eq_comm, and_comm]

private theorem BoundedCoordinates__optionCons_empty (a : Option ℕ) (xs : Option (List ℕ)) :
    some [] ≠ BoundedCoordinates__optionCons a xs := by
  cases a <;> cases xs <;> simp [BoundedCoordinates__optionCons]

private theorem BoundedCoordinates__option_tsum_split {α : Type*} (f : Option α → ENNReal) :
    (∑' x, f x) = f none + ∑' x, if x = none then 0 else f x := by
  classical
  refine (ENNReal.tsum_eq_add_tsum_ite (f := f) none).trans ?_
  congr 1
  apply tsum_congr
  intro x
  by_cases hx : x = none <;> simp [hx]

private theorem BoundedCoordinates__option_pmf_complement {α : Type*} (p : PMF (Option α)) :
    (∑' x, if x = none then 0 else p x) = 1 - p none := by
  classical
  have h := ENNReal.tsum_eq_add_tsum_ite (f := fun x => p x) none
  rw [p.tsum_coe] at h
  convert (ENNReal.sub_eq_of_eq_add_rev (p.apply_ne_top none) h).symm using 1
  apply tsum_congr
  intro x
  by_cases hx : x = none <;> simp [hx]

private theorem BoundedCoordinates__bounded_coordinates_failure_step (a D : ℕ) (Ds : List ℕ) :
    boundedCoordinates a (D :: Ds) none = boundedUniform D a none +
      (1 - boundedUniform D a none) * boundedCoordinates a Ds none := by
  classical
  let p := boundedUniform D a
  let q := boundedCoordinates a Ds
  change (p.bind fun x => q.map (BoundedCoordinates__optionCons x)) none = p none + (1 - p none) * q none
  rw [PMF.bind_apply]
  have inner (x : Option ℕ) : (q.map (BoundedCoordinates__optionCons x)) none =
      if x = none then 1 else q none := by
    rw [PMF.map_apply]
    simp only [BoundedCoordinates__optionCons_none]
    by_cases hx : x = none <;> simp [hx, q.tsum_coe]
  simp_rw [inner]
  rw [BoundedCoordinates__option_tsum_split]
  simp only [↓reduceIte, mul_one]
  congr 1
  calc
    (∑' x, if x = none then 0 else p x * (if x = none then 1 else q none)) =
        ∑' x, (if x = none then 0 else p x) * q none := by
      apply tsum_congr
      intro x
      by_cases hx : x = none <;> simp [hx]
    _ = (∑' x, if x = none then 0 else p x) * q none := ENNReal.tsum_mul_right
    _ = (1 - p none) * q none := by rw [BoundedCoordinates__option_pmf_complement]

private theorem BoundedCoordinates__bounded_coordinates_success_step (a D x : ℕ) (Ds xs : List ℕ) :
    boundedCoordinates a (D :: Ds) (some (x :: xs)) =
      boundedUniform D a (some x) * boundedCoordinates a Ds (some xs) := by
  classical
  let p := boundedUniform D a
  let q := boundedCoordinates a Ds
  change (p.bind fun y => q.map (BoundedCoordinates__optionCons y)) (some (x :: xs)) = p (some x) * q (some xs)
  rw [PMF.bind_apply]
  simp_rw [PMF.map_apply, BoundedCoordinates__optionCons_some, ite_and]
  have inner (y : Option ℕ) :
      (∑' ys, if y = some x then if ys = some xs then q ys else 0 else 0) =
        if y = some x then q (some xs) else 0 := by
    by_cases hy : y = some x <;> simp [hy]
  simp_rw [inner, mul_ite, mul_zero]
  simp

private theorem BoundedCoordinates__bounded_coordinates_empty_step (a D : ℕ) (Ds : List ℕ) :
    boundedCoordinates a (D :: Ds) (some []) = 0 := by
  classical
  change ((boundedUniform D a).bind fun y =>
    (boundedCoordinates a Ds).map (BoundedCoordinates__optionCons y)) (some []) = 0
  simp only [PMF.bind_apply, PMF.map_apply, BoundedCoordinates__optionCons_empty, if_false, tsum_zero, mul_zero]

private theorem BoundedCoordinates__bounded_uniform_normalized (D a : ℕ) (hD : 0 < D) (x : ℕ) :
    boundedUniform D a (some x) = (1 - boundedUniform D a none) *
      (if x < D then (D : ENNReal)⁻¹ else 0) := by
  have hzero : (D : ENNReal) ≠ 0 := by exact_mod_cast hD.ne'
  have h := congrArg (fun z : ENNReal => z * (D : ENNReal)⁻¹)
    ((bounded_uniform_law D a hD).2 x)
  rw [ENNReal.mul_inv_cancel_right hzero (by simp)] at h
  by_cases hx : x < D <;> simpa [hx] using h

private theorem BoundedCoordinates__bounded_coordinates_success_mass (a D : ℕ) (Ds : List ℕ) :
    1 - boundedCoordinates a (D :: Ds) none =
      (1 - boundedUniform D a none) * (1 - boundedCoordinates a Ds none) := by
  rw [BoundedCoordinates__bounded_coordinates_failure_step]
  rw [ENNReal.mul_sub (by intros; finiteness), mul_one, tsub_add_eq_tsub_tsub]

/-- Product rejection sampling: a union bound and exact conditional rectangular law. -/
theorem bounded_coordinates_law :
  ∀ (attempts : ℕ) (bounds : List ℕ),
  (∀ D ∈ bounds, 0 < D) →
  (boundedCoordinates attempts bounds) none ≤
    (bounds.length : ENNReal) * (2 : ENNReal)⁻¹ ^ attempts ∧
  ∀ xs : List ℕ,
    (boundedCoordinates attempts bounds) (some xs) =
      (1 - (boundedCoordinates attempts bounds) none) *
        (if List.Forall₂ (fun x D : ℕ => x < D) xs bounds then
          (bounds.map (fun D : ℕ => (D : ENNReal)⁻¹)).prod else 0) := by
  classical
  intro a bounds
  induction bounds with
  | nil =>
    intro _
    change (PMF.pure (some ([] : List ℕ))) none ≤ _ ∧
      ∀ xs, (PMF.pure (some ([] : List ℕ))) (some xs) =
        (1 - (PMF.pure (some ([] : List ℕ))) none) * _
    simp [PMF.pure_apply]
  | cons D Ds ih =>
    intro hpos
    have hD : 0 < D := hpos D (by simp)
    have hDs : ∀ E ∈ Ds, 0 < E := fun E hE => hpos E (by simp [hE])
    obtain ⟨hfail, hpoints⟩ := ih hDs
    constructor
    · calc
        boundedCoordinates a (D :: Ds) none = boundedUniform D a none +
            (1 - boundedUniform D a none) * boundedCoordinates a Ds none :=
          BoundedCoordinates__bounded_coordinates_failure_step a D Ds
        _ ≤ boundedUniform D a none + boundedCoordinates a Ds none := by
          apply add_le_add le_rfl
          calc
            (1 - boundedUniform D a none) * boundedCoordinates a Ds none ≤
                1 * boundedCoordinates a Ds none :=
              mul_le_mul (tsub_le_self : 1 - boundedUniform D a none ≤ 1)
                le_rfl zero_le zero_le
            _ = boundedCoordinates a Ds none := one_mul _
        _ ≤ (2 : ENNReal)⁻¹ ^ a + (Ds.length : ENNReal) * (2 : ENNReal)⁻¹ ^ a :=
          add_le_add (bounded_uniform_law D a hD).1 hfail
        _ = ((D :: Ds).length : ENNReal) * (2 : ENNReal)⁻¹ ^ a := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          ac_rfl
    · intro xs
      cases xs with
      | nil => rw [BoundedCoordinates__bounded_coordinates_empty_step]; simp
      | cons x xs =>
        rw [BoundedCoordinates__bounded_coordinates_success_step, BoundedCoordinates__bounded_uniform_normalized D a hD,
          hpoints xs, BoundedCoordinates__bounded_coordinates_success_mass]
        by_cases hx : x < D <;>
          by_cases hxs : List.Forall₂ (fun x D : ℕ => x < D) xs Ds <;>
          simp [hx, hxs, List.forall₂_cons] <;> ac_rfl

end GenericGroupWE.Main


-- Exact source with hygienic private names: WitnessEncryption.CoordinateListCodec

namespace GenericGroupWE.Main

private abbrev CoordinateListCodec__CoordinateTriple (m k : ℕ) (p : PrimeOrder) :=
  (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin k → ZMod p.val)

private def CoordinateListCodec__coordinateList {m k : ℕ} {p : PrimeOrder} (z : CoordinateListCodec__CoordinateTriple m k p) : List ℕ :=
  List.ofFn (fun i => (z.1 i).val) ++ List.ofFn (fun i => (z.2.1 i).val) ++
    List.ofFn (fun i => (z.2.2 i).val)

private theorem CoordinateListCodec__getD_ofFn {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem (List.ofFn f) d (by simpa using i.isLt), List.getElem_ofFn]

private theorem CoordinateListCodec__coordinate_list_first {m k : ℕ} {p : PrimeOrder}
    (z : CoordinateListCodec__CoordinateTriple m k p) (i : Fin m) :
    ((CoordinateListCodec__coordinateList z).getD i.val 0 : ZMod p.val) = z.1 i := by
  dsimp [CoordinateListCodec__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append _ _ _ _ (by simpa using i.isLt), CoordinateListCodec__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem CoordinateListCodec__coordinate_list_middle {m k : ℕ} {p : PrimeOrder}
    (z : CoordinateListCodec__CoordinateTriple m k p) (i : Fin m) :
    (CoordinateListCodec__coordinateList z).getD (m+i.val) 0 = (z.2.1 i).val := by
  dsimp [CoordinateListCodec__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  exact CoordinateListCodec__getD_ofFn _ i _

private theorem CoordinateListCodec__coordinate_list_last {m k : ℕ} {p : PrimeOrder}
    (z : CoordinateListCodec__CoordinateTriple m k p) (i : Fin k) :
    ((CoordinateListCodec__coordinateList z).getD (2*m+i.val) 0 : ZMod p.val) = z.2.2 i := by
  dsimp [CoordinateListCodec__coordinateList]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 2*m+i.val-(m+m) = i.val by omega, CoordinateListCodec__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem CoordinateListCodec__coordinate_list_injective (m k : ℕ) (p : PrimeOrder) :
    Function.Injective (CoordinateListCodec__coordinateList (m := m) (k := k) (p := p)) := by
  intro z w h
  apply Prod.ext
  · funext i
    have hi := congrArg (fun xs : List ℕ => (xs.getD i.val 0 : ZMod p.val)) h
    simpa only [CoordinateListCodec__coordinate_list_first] using hi
  · apply Prod.ext
    · funext i
      apply Fin.ext
      have hi := congrArg (fun xs : List ℕ => xs.getD (m+i.val) 0) h
      simpa only [CoordinateListCodec__coordinate_list_middle] using hi
    · funext i
      have hi := congrArg (fun xs : List ℕ => (xs.getD (2*m+i.val) 0 : ZMod p.val)) h
      simpa only [CoordinateListCodec__coordinate_list_last] using hi

private theorem CoordinateListCodec__ofFn_lt_replicate (N D : ℕ) (f : Fin N → ℕ) (hf : ∀ i, f i < D) :
    List.Forall₂ (fun x d : ℕ => x < d) (List.ofFn f) (List.replicate N D) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi1 hi2
  have hi : i < N := by simpa using hi1
  rw [← List.getD_eq_get (List.ofFn f) 0 ⟨i,hi1⟩,
    ← List.getD_eq_get (List.replicate N D) 0 ⟨i,hi2⟩,
    CoordinateListCodec__getD_ofFn f ⟨i,hi⟩ 0, List.getD_replicate D hi]
  exact hf _

private theorem CoordinateListCodec__coordinate_list_valid {m k : ℕ} {p : PrimeOrder}
    (z : CoordinateListCodec__CoordinateTriple m k p) :
    List.Forall₂ (fun x D : ℕ => x < D) (CoordinateListCodec__coordinateList z) (coordinateBounds m k p.val) := by
  exact List.rel_append
    (List.rel_append (CoordinateListCodec__ofFn_lt_replicate m p.val _ (fun i => ZMod.val_lt _))
      (CoordinateListCodec__ofFn_lt_replicate m m _ (fun i => (z.2.1 i).isLt)))
    (CoordinateListCodec__ofFn_lt_replicate k p.val _ (fun i => ZMod.val_lt _))

private theorem CoordinateListCodec__vector_of_bounded_list (N D : ℕ) (xs : List ℕ)
    (h : List.Forall₂ (fun x d : ℕ => x < d) xs (List.replicate N D)) :
    ∃ f : Fin N → Fin D, List.ofFn (fun i => (f i).val) = xs := by
  have hlen : xs.length = N := by simpa using h.length_eq
  have hbound (i : Fin N) : xs.getD i.val 0 < D := by
    have hi : i.val < xs.length := by omega
    have hc := h.get hi (by simpa using i.isLt)
    rw [← List.getD_eq_get xs 0 ⟨i.val,hi⟩,
      ← List.getD_eq_get (List.replicate N D) 0 ⟨i.val,by simpa using i.isLt⟩,
      List.getD_replicate D i.isLt] at hc
    exact hc
  let f : Fin N → Fin D := fun i => ⟨xs.getD i.val 0, hbound i⟩
  refine ⟨f, ?_⟩
  apply List.ext_getElem
  · simpa using hlen.symm
  · intro i hi1 hi2
    rw [List.getElem_ofFn]
    exact List.getD_eq_getElem xs 0 hi2

private theorem CoordinateListCodec__coordinate_list_surjective (m k : ℕ) (p : PrimeOrder) (xs : List ℕ)
    (h : List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m k p.val)) :
    ∃ z : CoordinateListCodec__CoordinateTriple m k p, CoordinateListCodec__coordinateList z = xs := by
  have hright : List.Forall₂ (fun x D : ℕ => x < D) xs
      (List.replicate m p.val ++ (List.replicate m m ++ List.replicate k p.val)) := by
    simpa only [coordinateBounds, List.append_assoc] using h
  have hs := List.forall₂_take_append xs (List.replicate m p.val)
    (List.replicate m m ++ List.replicate k p.val) hright
  have hrest := List.forall₂_drop_append xs (List.replicate m p.val)
    (List.replicate m m ++ List.replicate k p.val) hright
  simp only [List.length_replicate] at hs hrest
  have hr := List.forall₂_take_append (xs.drop m) (List.replicate m m)
    (List.replicate k p.val) hrest
  have ht := List.forall₂_drop_append (xs.drop m) (List.replicate m m)
    (List.replicate k p.val) hrest
  simp only [List.length_replicate] at hr ht
  obtain ⟨s,hs⟩ := CoordinateListCodec__vector_of_bounded_list m p.val (xs.take m) hs
  obtain ⟨r,hr⟩ := CoordinateListCodec__vector_of_bounded_list m m ((xs.drop m).take m) hr
  obtain ⟨t,ht⟩ := CoordinateListCodec__vector_of_bounded_list k p.val ((xs.drop m).drop m) ht
  let z : CoordinateListCodec__CoordinateTriple m k p :=
    (fun i => ((s i).val : ZMod p.val), r, fun i => ((t i).val : ZMod p.val))
  refine ⟨z, ?_⟩
  have hscast : List.ofFn (fun i => ((s i).val : ZMod p.val).val) =
      List.ofFn (fun i => (s i).val) := by
    congr 1
    funext i
    exact ZMod.val_natCast_of_lt (s i).isLt
  have htcast : List.ofFn (fun i => ((t i).val : ZMod p.val).val) =
      List.ofFn (fun i => (t i).val) := by
    congr 1
    funext i
    exact ZMod.val_natCast_of_lt (t i).isLt
  change (List.ofFn (fun i => ((s i).val : ZMod p.val).val) ++
    List.ofFn (fun i => (r i).val)) ++
    List.ofFn (fun i => ((t i).val : ZMod p.val).val) = xs
  rw [hscast, htcast, hs, hr, ht, List.append_assoc,
    List.take_append_drop, List.take_append_drop]

theorem coordinate_list_codec :
  ∀ (m k : ℕ) (p : PrimeOrder),
  let encode : ((Fin m → ZMod p.val) × (Fin m → Fin m) ×
      (Fin k → ZMod p.val)) → List ℕ := fun z =>
    List.ofFn (fun i => (z.1 i).val) ++
    List.ofFn (fun i => (z.2.1 i).val) ++
    List.ofFn (fun i => (z.2.2 i).val)
  Function.Injective encode ∧
    ∀ xs : List ℕ, (∃ z, encode z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m k p.val) := by
  intro m k p
  change Function.Injective (CoordinateListCodec__coordinateList (m := m) (k := k) (p := p)) ∧
    ∀ xs : List ℕ, (∃ z : CoordinateListCodec__CoordinateTriple m k p, CoordinateListCodec__coordinateList z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m k p.val)
  refine ⟨CoordinateListCodec__coordinate_list_injective m k p, ?_⟩
  intro xs
  constructor
  · rintro ⟨z,rfl⟩
    exact CoordinateListCodec__coordinate_list_valid z
  · exact CoordinateListCodec__coordinate_list_surjective m k p xs


end GenericGroupWE.Main


-- Exact source with hygienic private names: WitnessEncryption.SamplingDistribution

open scoped ENNReal BigOperators
namespace GenericGroupWE.Main

private theorem SamplingDistribution__coordinate_bounds_positive (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (k : ℕ) :
    ∀ D ∈ coordinateBounds m k p.val, 0 < D := by
  intro D hD
  have hp := p.property.pos
  simp only [coordinateBounds, List.mem_append, List.mem_replicate] at hD
  omega

private theorem SamplingDistribution__coordinate_bounds_length (m k p : ℕ) :
    (coordinateBounds m k p).length = 2*m+k := by
  simp [coordinateBounds]
  omega

private theorem SamplingDistribution__sampling_failure_bound (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (n : ℕ) :
    samplingFailure B n ≤ (2 : ℝ)^(-(n : ℝ)-2) := by
  have hv := (bounded_coordinates_law (coordinateAttempts n m B.k)
    (coordinateBounds m B.k p.val) (SamplingDistribution__coordinate_bounds_positive m hm p B.k)).1
  have hreal := ENNReal.toReal_mono (by finiteness) hv
  simp only [SamplingDistribution__coordinate_bounds_length, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at hreal
  unfold samplingFailure probability
  change ((samplingLaw B n).toOuterMeasure {none}).toReal ≤ _
  rw [PMF.toOuterMeasure_apply_singleton]
  have hc : (2*m+B.k : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (2*m+B.k) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2*m+B.k)
  have hrpow : (2 : ℝ)^(-(n : ℝ)-2) = ((2 : ℝ)^(n+2))⁻¹ := by
    rw [show -(n : ℝ)-2 = -((n+2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg (by positivity), Real.rpow_natCast]
  calc
    ((samplingLaw B n) none).toReal ≤
        (2*m+B.k : ℝ) * (2 : ℝ)⁻¹ ^ coordinateAttempts n m B.k := by
          simpa only [samplingLaw, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hreal
    _ ≤ (2 : ℝ)^Nat.clog 2 (2*m+B.k) * (2 : ℝ)⁻¹ ^ coordinateAttempts n m B.k :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (2 : ℝ)^(-(n : ℝ)-2) := by
      rw [hrpow]
      simp only [coordinateAttempts, pow_add, inv_pow]
      field_simp
      <;> ring

private theorem SamplingDistribution__option_tsum (α : Type*) (f : Option α → ENNReal) :
    (∑' x, f x) = f none + ∑' x, f (some x) := by
  classical
  rw [ENNReal.tsum_eq_add_tsum_ite none]
  congr 1
  have h := Function.Injective.tsum_eq (g := fun x : α => some x)
    (fun a b h => Option.some.inj h)
    (f := fun x : Option α => if x = none then 0 else f x) (by
      intro x hx
      cases x with
      | none => simp at hx
      | some x => exact ⟨x,rfl⟩)
  have hn : (∑' x : Option α, if x = none then 0 else f x) =
      ∑' x, f (some x) := by simpa using h.symm
  convert hn using 1
  apply tsum_congr
  intro x
  by_cases hx : x = none <;> simp [hx]

private theorem SamplingDistribution__coordinate_ciphertext_not_abort (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
    (t : Fin B.k → ZMod p.val) (message : Bool) :
    abortCiphertext ≠ coordinateCiphertext B σ s r t message := by
  intro h
  have houtput := congrArg Ciphertext.output h
  simp [abortCiphertext, coordinateCiphertext] at houtput

private theorem SamplingDistribution__sampling_abort_mass (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (n : ℕ) (message : Bool) :
    (boundedEncryption B n message) abortCiphertext = (samplingLaw B n) none := by
  classical
  rw [boundedEncryption, PMF.bind_apply, SamplingDistribution__option_tsum]
  change (samplingLaw B n) none * (PMF.pure abortCiphertext) abortCiphertext + _ = _
  simp only [PMF.pure_apply, ↓reduceIte, mul_one]
  suffices (∑' xs : List ℕ, (samplingLaw B n) (some xs) *
    ((PMF.uniformOfFintype (Encoding p.val)).map fun σ =>
      coordinateCiphertext B σ (fun i => (xs.getD i.val 0 : ZMod p.val))
        (fun i => xs.getD (m+i.val) 0 + 1)
        (fun j => (xs.getD (2*m+j.val) 0 : ZMod p.val)) message) abortCiphertext) = 0 by
    rw [this, add_zero]
  apply ENNReal.tsum_eq_zero.mpr
  intro xs
  rw [PMF.map_apply]
  have hzero : (∑' σ : Encoding p.val,
      if abortCiphertext = coordinateCiphertext B σ
        (fun i => (xs.getD i.val 0 : ZMod p.val))
        (fun i => xs.getD (m+i.val) 0 + 1)
        (fun j => (xs.getD (2*m+j.val) 0 : ZMod p.val)) message
      then PMF.uniformOfFintype (Encoding p.val) σ else 0) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro σ
    exact if_neg (SamplingDistribution__coordinate_ciphertext_not_abort m p B σ _ _ _ message)
  rw [hzero, mul_zero]

private abbrev SamplingDistribution__CoordinateTriple (m k : ℕ) (p : PrimeOrder) :=
  (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin k → ZMod p.val)

private def SamplingDistribution__coordinateList {m k : ℕ} {p : PrimeOrder} (z : SamplingDistribution__CoordinateTriple m k p) : List ℕ :=
  List.ofFn (fun i => (z.1 i).val) ++ List.ofFn (fun i => (z.2.1 i).val) ++
    List.ofFn (fun i => (z.2.2 i).val)

private theorem SamplingDistribution__getD_ofFn {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem (List.ofFn f) d (by simpa using i.isLt), List.getElem_ofFn]

private theorem SamplingDistribution__coordinate_list_first {m k : ℕ} {p : PrimeOrder}
    (z : SamplingDistribution__CoordinateTriple m k p) (i : Fin m) :
    ((SamplingDistribution__coordinateList z).getD i.val 0 : ZMod p.val) = z.1 i := by
  dsimp [SamplingDistribution__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append _ _ _ _ (by simpa using i.isLt), SamplingDistribution__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem SamplingDistribution__coordinate_list_middle {m k : ℕ} {p : PrimeOrder}
    (z : SamplingDistribution__CoordinateTriple m k p) (i : Fin m) :
    (SamplingDistribution__coordinateList z).getD (m+i.val) 0 = (z.2.1 i).val := by
  dsimp [SamplingDistribution__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  exact SamplingDistribution__getD_ofFn _ i _

private theorem SamplingDistribution__coordinate_list_last {m k : ℕ} {p : PrimeOrder}
    (z : SamplingDistribution__CoordinateTriple m k p) (i : Fin k) :
    ((SamplingDistribution__coordinateList z).getD (2*m+i.val) 0 : ZMod p.val) = z.2.2 i := by
  dsimp [SamplingDistribution__coordinateList]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 2*m+i.val-(m+m) = i.val by omega, SamplingDistribution__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem SamplingDistribution__coordinate_card_inverse (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (k : ℕ) :
    (Fintype.card (SamplingDistribution__CoordinateTriple m k p) : ENNReal)⁻¹ =
      ((coordinateBounds m k p.val).map (fun D : ℕ => (D : ENNReal)⁻¹)).prod := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hp0 : (p.val : ENNReal) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hc0 : (Fintype.card (SamplingDistribution__CoordinateTriple m k p) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by
    simp only [coordinateBounds, List.map_append, List.map_replicate,
      List.prod_append, List.prod_replicate]
    finiteness)).mp
  simp [SamplingDistribution__CoordinateTriple, coordinateBounds, Fintype.card_fun,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  <;> ring

private theorem SamplingDistribution__exact_coordinate_list_law (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p)
    (hinj : Function.Injective (SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)))
    (hrange : ∀ xs : List ℕ, (∃ z : SamplingDistribution__CoordinateTriple m B.k p, SamplingDistribution__coordinateList z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val))
    (xs : List ℕ) :
    ((exactCoordinates B hm).map SamplingDistribution__coordinateList) xs =
      if List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val) then
        ((coordinateBounds m B.k p.val).map (fun D : ℕ => (D : ENNReal)⁻¹)).prod else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hx : List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val)
  · obtain ⟨z, hz⟩ := (hrange xs).mpr hx
    subst xs
    simp only [hinj.eq_iff, tsum_ite_eq', hx, ↓reduceIte]
    simpa only [exactCoordinates, PMF.uniformOfFintype_apply] using
      SamplingDistribution__coordinate_card_inverse m hm p B.k
  · rw [if_neg hx]
    apply ENNReal.tsum_eq_zero.mpr
    intro z
    apply if_neg
    intro hz
    exact hx ((hrange xs).mp ⟨z,hz.symm⟩)

private noncomputable def listEncryption {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (message : Bool) (xs : List ℕ) : PMF Ciphertext :=
  (PMF.uniformOfFintype (Encoding p.val)).map fun σ =>
    coordinateCiphertext B σ (fun i => (xs.getD i.val 0 : ZMod p.val))
      (fun i => xs.getD (m+i.val) 0 + 1)
      (fun j => (xs.getD (2*m+j.val) 0 : ZMod p.val)) message

private theorem SamplingDistribution__list_encryption_encode (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (message : Bool) (z : SamplingDistribution__CoordinateTriple m B.k p) :
    listEncryption B message (SamplingDistribution__coordinateList z) =
      (PMF.uniformOfFintype (Encoding p.val)).map fun σ =>
        coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message := by
  simp only [listEncryption, SamplingDistribution__coordinate_list_first, SamplingDistribution__coordinate_list_middle, SamplingDistribution__coordinate_list_last]

private theorem SamplingDistribution__list_encryption_ideal (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (message : Bool) :
    ((exactCoordinates B hm).map SamplingDistribution__coordinateList).bind (listEncryption B message) =
      idealEncryption B hm message := by
  rw [PMF.bind_map]
  change ((exactCoordinates B hm).bind fun z => listEncryption B message (SamplingDistribution__coordinateList z)) = _
  simp only [SamplingDistribution__list_encryption_encode]
  change ((exactCoordinates B hm).bind fun z =>
    (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
      PMF.pure (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message)) =
    (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
      (exactCoordinates B hm).bind fun z =>
        PMF.pure (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message)
  exact PMF.bind_comm _ _ _

private theorem SamplingDistribution__sampling_success_from_codec (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (n : ℕ)
    (hinj : Function.Injective (SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)))
    (hrange : ∀ xs : List ℕ, (∃ z : SamplingDistribution__CoordinateTriple m B.k p, SamplingDistribution__coordinateList z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val))
    (message : Bool) (C : Ciphertext) (hC : C.output.isSome) :
    (boundedEncryption B n message) C =
      (1 - (samplingLaw B n) none) * (idealEncryption B hm message) C := by
  classical
  have habort : C ≠ abortCiphertext := by
    intro h
    subst C
    simp [abortCiphertext] at hC
  have hsample (xs : List ℕ) :
      (samplingLaw B n) (some xs) = (1 - (samplingLaw B n) none) *
        ((exactCoordinates B hm).map SamplingDistribution__coordinateList) xs := by
    change (boundedCoordinates (coordinateAttempts n m B.k) (coordinateBounds m B.k p.val))
      (some xs) = _
    rw [(bounded_coordinates_law (coordinateAttempts n m B.k)
      (coordinateBounds m B.k p.val) (SamplingDistribution__coordinate_bounds_positive m hm p B.k)).2 xs,
      SamplingDistribution__exact_coordinate_list_law m hm p B hinj hrange xs]
    rfl
  rw [boundedEncryption, PMF.bind_apply, SamplingDistribution__option_tsum]
  change (samplingLaw B n) none * (PMF.pure abortCiphertext) C +
    (∑' xs, (samplingLaw B n) (some xs) * listEncryption B message xs C) = _
  simp only [PMF.pure_apply, if_neg habort, mul_zero, zero_add]
  simp_rw [hsample, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  change (1 - (samplingLaw B n) none) *
    (((exactCoordinates B hm).map SamplingDistribution__coordinateList).bind (listEncryption B message)) C = _
  rw [SamplingDistribution__list_encryption_ideal]

theorem bounded_sampling_distribution :
  ∀ (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p) (n : ℕ),
  samplingFailure B n ≤ (2 : ℝ)^(-(n : ℝ)-2) ∧
  (∀ message : Bool,
    (boundedEncryption B n message) abortCiphertext = (samplingLaw B n) none) ∧
  (∀ (message : Bool) (C : Ciphertext), C.output.isSome →
    (boundedEncryption B n message) C =
      (1 - (samplingLaw B n) none) * (idealEncryption B hm message) C) := by
  intro m hm p B n
  obtain ⟨hinj,hrange⟩ := coordinate_list_codec m B.k p
  change Function.Injective (SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)) at hinj
  change (∀ xs : List ℕ, (∃ z : SamplingDistribution__CoordinateTriple m B.k p, SamplingDistribution__coordinateList z = xs) ↔
    List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val)) at hrange
  exact ⟨SamplingDistribution__sampling_failure_bound m hm p B n, SamplingDistribution__sampling_abort_mass m p B n,
    SamplingDistribution__sampling_success_from_codec m hm p B n hinj hrange⟩

end GenericGroupWE.Main


-- Exact source with hygienic private names: WitnessEncryption.BoundedEncryptionTransfer

namespace GenericGroupWE.Main
open scoped BigOperators
namespace CorrectnessProof

lemma honest_output_some (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
    (t : Fin B.k → ZMod p.val) (message : Bool) :
    (coordinateCiphertext B σ s r t message).output.isSome := by
  simp [coordinateCiphertext]

lemma map_no_output_zero {ι : Type*} (law : PMF ι) (f : ι → Ciphertext)
    (hf : ∀ i, (f i).output.isSome) (C : Ciphertext) (hC : C.output = none) :
    (law.map f) C = 0 := by
  classical
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro i
  apply if_neg
  intro heq
  have hi := hf i
  rw [← heq, hC] at hi
  contradiction

lemma ideal_no_output_zero (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (message : Bool) (C : Ciphertext) (hC : C.output = none) :
    (idealEncryption B hm message) C = 0 := by
  rw [idealEncryption, PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro σ
  apply mul_eq_zero.mpr
  right
  apply map_no_output_zero
  · intro z
    exact honest_output_some m p B σ z.1 _ z.2.2 message
  · exact hC

lemma bounded_no_output_zero (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (n : ℕ) (message : Bool) (C : Ciphertext) (hC : C.output = none) (hne : C ≠ abortCiphertext) :
    (boundedEncryption B n message) C = 0 := by
  classical
  rw [boundedEncryption, PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  cases result with
  | none =>
    change (samplingLaw B n) none*(PMF.pure abortCiphertext) C = 0
    rw [PMF.pure_apply, if_neg hne, mul_zero]
  | some xs =>
    rw [map_no_output_zero _ _ (fun σ => honest_output_some m p B σ _ _ _ message) C hC, mul_zero]

lemma pmf_event_finite {ι : Type*} (law : PMF ι) (E : Set ι) :
    law.toOuterMeasure E ≠ ⊤ := by
  have hu : law.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa using law.tsum_coe
  have hle : law.toOuterMeasure E ≤ 1 := by
    rw [← hu]
    exact law.toOuterMeasure.mono (Set.subset_univ _)
  exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)

end CorrectnessProof

theorem bounded_encryption_event_transfer :
    ∀ (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p) (n : ℕ)
      (message : Bool) (event : Ciphertext → Prop),
      probability (boundedEncryption B n message) event ≤
        samplingFailure B n + probability (idealEncryption B hm message) event := by
  intro m hm p B n message event
  classical
  have hdist := bounded_sampling_distribution m hm p B n
  let δ := (samplingLaw B n) none
  have hpoint : ∀ C : Ciphertext,
      (boundedEncryption B n message) C ≤
        δ*(PMF.pure abortCiphertext) C + (idealEncryption B hm message) C := by
    intro C
    cases hC : C.output with
    | none =>
      by_cases heq : C = abortCiphertext
      · subst C
        rw [hdist.2.1 message]
        simp only [PMF.pure_apply, ↓reduceIte, mul_one]
        exact le_add_right le_rfl
      · rw [CorrectnessProof.bounded_no_output_zero m p B n message C hC heq]
        exact bot_le
    | some out =>
      have hsome : C.output.isSome := by simp [hC]
      rw [hdist.2.2 message C hsome]
      have hne : C ≠ abortCiphertext := by
        intro h
        rw [h] at hC
        simp [abortCiphertext] at hC
      simp only [PMF.pure_apply, if_neg hne, mul_zero, zero_add]
      calc
        (1-(samplingLaw B n) none)*(idealEncryption B hm message) C ≤
            1*(idealEncryption B hm message) C := by
          simpa only [mul_comm] using mul_le_mul_right
            (show (1 : ENNReal)-(samplingLaw B n) none ≤ 1 from tsub_le_self)
            ((idealEncryption B hm message) C)
        _ = _ := one_mul _
  have hsum : (boundedEncryption B n message).toOuterMeasure {C | event C} ≤
      δ + (idealEncryption B hm message).toOuterMeasure {C | event C} := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    calc
      (∑' C, Set.indicator {C | event C} (boundedEncryption B n message) C) ≤
          ∑' C, (δ*(PMF.pure abortCiphertext) C +
            Set.indicator {C | event C} (idealEncryption B hm message) C) := by
        apply ENNReal.tsum_le_tsum
        intro C
        change (if event C then (boundedEncryption B n message) C else 0) ≤
          δ*(PMF.pure abortCiphertext) C + (if event C then (idealEncryption B hm message) C else 0)
        by_cases he : event C
        · simpa only [if_pos he] using hpoint C
        · rw [if_neg he]
          exact bot_le
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  unfold probability samplingFailure
  change _ ≤ ((samplingLaw B n).toOuterMeasure {none}).toReal + _
  rw [PMF.toOuterMeasure_apply_singleton]
  apply ENNReal.toReal_le_add hsum
  · change (samplingLaw B n) none ≠ ⊤
    rw [← PMF.toOuterMeasure_apply_singleton]
    exact CorrectnessProof.pmf_event_finite _ _
  · exact CorrectnessProof.pmf_event_finite _ _

end GenericGroupWE.Main

-- Exact source with hygienic private names: WitnessEncryption.UniformAffineTest

namespace GenericGroupWE.Main
open scoped BigOperators

namespace FixedTestProof

lemma uniform_probability {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop) :
    probability (PMF.uniformOfFintype ι) event =
      (Nat.card {x : ι | event x} : ℝ) / (Fintype.card ι : ℝ) := by
  classical
  unfold probability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ← Nat.card_eq_fintype_card]

lemma short_cast_injective (m : ℕ) (p : PrimeOrder) (hp : m ≤ p.val) :
    Function.Injective (fun r : Fin m => ((r.val+1 : ℕ) : ZMod p.val)) := by
  intro r s h
  have he : (r.val : ZMod p.val) = (s.val : ZMod p.val) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_left_inj] using h
  apply Fin.ext
  have hr : r.val < p.val := r.isLt.trans_le hp
  have hs : s.val < p.val := s.isLt.trans_le hp
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] using hv

lemma trivial_test (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (message : Bool) : fixedTestProbability B hm 0 0 0 message = 1 := by
  unfold fixedTestProbability probability
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  simp
  simpa only [tsum_fintype, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (exactCoordinates B hm).tsum_coe

lemma uniform_probability_sum {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop)
    [DecidablePred event] :
    probability (PMF.uniformOfFintype ι) event =
      (∑ x : ι, if event x then (1 : ℝ) else 0) / (Fintype.card ι : ℝ) := by
  classical
  rw [uniform_probability]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Set.mem_ofPred_eq]

lemma uniform_probability_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (e : ι ≃ κ) (event : κ → Prop) :
    probability (PMF.uniformOfFintype ι) (fun x => event (e x)) =
      probability (PMF.uniformOfFintype κ) event := by
  classical
  rw [uniform_probability_sum, uniform_probability_sum, Fintype.card_congr e]
  congr 1
  exact e.sum_comp (fun x => if event x then (1 : ℝ) else 0)

lemma uniform_probability_prod {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι × κ → Prop) :
    probability (PMF.uniformOfFintype (ι × κ)) event =
      (∑ x : ι, probability (PMF.uniformOfFintype κ) (fun y => event (x,y))) /
        (Fintype.card ι : ℝ) := by
  classical
  simp only [uniform_probability_sum, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul,
    ← Finset.sum_div]
  ring


lemma uniform_probability_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop) :
    probability (PMF.uniformOfFintype ι) event ≤ 1 := by
  classical
  rw [uniform_probability_sum]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  calc
    (∑ x : ι, if event x then (1 : ℝ) else 0) ≤ ∑ _x : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> norm_num
    _ = _ := by simp

lemma uniform_probability_const {ι : Type*} [Fintype ι] [Nonempty ι] (P : Prop) [Decidable P] :
    probability (PMF.uniformOfFintype ι) (fun _ => P) = if P then 1 else 0 := by
  classical
  rw [uniform_probability_sum]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs <;> simp_all

lemma uniform_ignore_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι → Prop) :
    probability (PMF.uniformOfFintype (ι × κ)) (fun x => event x.1) =
      probability (PMF.uniformOfFintype ι) event := by
  classical
  rw [uniform_probability_prod, uniform_probability_sum]
  simp only [uniform_probability_const]

lemma uniform_condition_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι × κ → Prop) (bad : ι → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ x, ¬ bad x → probability (PMF.uniformOfFintype κ) (fun y => event (x,y)) ≤ δ) :
    probability (PMF.uniformOfFintype (ι × κ)) event ≤
      probability (PMF.uniformOfFintype ι) bad + δ := by
  classical
  have hpoint : ∀ x : ι,
      probability (PMF.uniformOfFintype κ) (fun y => event (x,y)) ≤
        (if bad x then (1 : ℝ) else 0) + δ := by
    intro x
    by_cases hx : bad x
    · simpa only [if_pos hx] using
        (uniform_probability_le_one (fun y => event (x,y))).trans (by linarith : (1:ℝ) ≤ 1+δ)
    · simpa only [if_neg hx, zero_add] using hgood x hx
  rw [uniform_probability_prod, uniform_probability_sum]
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    (∑ x : ι, probability (PMF.uniformOfFintype κ) (fun y => event (x,y))) / (Fintype.card ι : ℝ) ≤
        (∑ x : ι, ((if bad x then (1 : ℝ) else 0)+δ)) / (Fintype.card ι : ℝ) := by
      apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hpoint x) hcard.le
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      field_simp


end FixedTestProof

theorem uniform_affine_test_bound :
    ∀ (p : PrimeOrder) (ι : Type*) [Fintype ι] [DecidableEq ι]
      (α : ZMod p.val) (β : ι → ZMod p.val),
      ¬ (α = 0 ∧ β = 0) →
        probability (PMF.uniformOfFintype (ι → ZMod p.val))
          (fun s => α + ∑ i, β i * s i = 0) ≤ (p.val : ℝ)⁻¹ := by
  intro p ι _ _ α β hnonzero
  classical
  by_cases hβ : β = 0
  · have hα : α ≠ 0 := fun h => hnonzero ⟨h,hβ⟩
    simp [probability, hβ, hα]
  · obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by simpa [funext_iff] using hβ
    let O := {j : ι // j ≠ i}
    let S : Set (ι → ZMod p.val) := {s | α + ∑ j, β j * s j = 0}
    let restrict : S → (O → ZMod p.val) := fun s j => s.val j.val
    have hinj : Function.Injective restrict := by
      intro x y hxy
      have hother : ∀ j : ι, j ≠ i → x.val j = y.val j := by
        intro j hj
        exact congrFun hxy ⟨j,hj⟩
      have hs : (∑ j, β j * (x.val j-y.val j)) = β i * (x.val i-y.val i) := by
        apply Fintype.sum_eq_single i
        intro j hj
        rw [hother j hj, sub_self, mul_zero]
      have hz : (∑ j, β j * (x.val j-y.val j)) = 0 := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        have hx := x.property
        have hy := y.property
        dsimp [S] at hx hy
        linear_combination hx - hy
      have hpivot : x.val i = y.val i := sub_eq_zero.mp ((mul_eq_zero.mp (hs.symm.trans hz)).resolve_left hi)
      apply Subtype.ext
      funext j
      by_cases hj : j = i
      · simpa [hj] using hpivot
      · exact hother j hj
    have hcard : Nat.card S ≤ p.val^(Fintype.card O) := by
      have h := Nat.card_le_card_of_injective restrict hinj
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] using h
    have hdim : Fintype.card ι = Fintype.card O+1 := by
      simpa only [Fintype.card_option, O] using
        (Fintype.card_congr (Equiv.optionSubtypeNe i)).symm
    have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
    rw [FixedTestProof.uniform_probability]
    change (Nat.card S : ℝ)/(Fintype.card (ι → ZMod p.val) : ℝ) ≤ (p.val : ℝ)⁻¹
    simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow]
    calc
      (Nat.card S : ℝ)/(p.val : ℝ)^(Fintype.card ι) ≤
          (p.val : ℝ)^(Fintype.card O)/(p.val : ℝ)^(Fintype.card ι) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
      _ = (p.val : ℝ)⁻¹ := by
        rw [hdim, pow_succ]
        field_simp

end GenericGroupWE.Main

-- Exact source with hygienic private names: WitnessEncryption.CorrectnessBounds

namespace GenericGroupWE.Main

private theorem CorrectnessBounds__odd_square_le_two_pow (k : ℕ) (hk : 16 ≤ k) :
    (2*k+1)^2 ≤ 2^k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      calc
        (2*(k+1)+1)^2 ≤ 2 * (2*k+1)^2 := by nlinarith
        _ ≤ 2 * 2^k := Nat.mul_le_mul_left 2 ih
        _ = 2^(k+1) := by simp [pow_succ, Nat.mul_comm]

private theorem CorrectnessBounds__weighted_square_le_two_pow (n m : ℕ) (hn : 2 ≤ n) (hm : 16*n ≤ m) :
    m^2 * (2 * 2^n) ≤ 2^m := by
  have hhalf : 16 ≤ m/2 := by omega
  have hmhalf : m ≤ 2*(m/2)+1 := by omega
  have hsq : m^2 ≤ 2^(m/2) :=
    (Nat.pow_le_pow_left hmhalf 2).trans (CorrectnessBounds__odd_square_le_two_pow (m/2) hhalf)
  have hexp : m/2 + (n+1) ≤ m := by omega
  calc
    m^2 * (2 * 2^n) ≤ 2^(m/2) * 2^(n+1) := by
      simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_right (2 * 2^n) hsq
    _ = 2^(m/2+(n+1)) := (pow_add 2 (m/2) (n+1)).symm
    _ ≤ 2^m := Nat.pow_le_pow_right (by decide) hexp

/-- The numerical slack in Proposition 3.3, isolated from the probability law. -/
theorem correctness_error_bound (n m : ℕ) (hn : 2 ≤ n) (hm : 16*n ≤ m)
    (δ : ℝ) (hδ : δ ≤ (2 : ℝ)^(-(n : ℝ)-2)) :
    δ + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ≤ (2 : ℝ)^(-(n : ℝ)) := by
  have hnpos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
  have hmpos : (0 : ℝ) < 2^m := pow_pos (by norm_num) m
  have hnat := CorrectnessBounds__weighted_square_le_two_pow n m hn hm
  have hcast : (m : ℝ)^2 * (2 * (2 : ℝ)^n) ≤ (2 : ℝ)^m := by
    exact_mod_cast hnat
  have htail : (m : ℝ)^2 / (2 : ℝ)^m ≤ 1 / (2 * (2 : ℝ)^n) := by
    apply (div_le_div_iff₀ hmpos (by positivity : (0 : ℝ) < 2 * (2 : ℝ)^n)).2
    simpa using hcast
  have hexpn : (2 : ℝ)^(-(n : ℝ)) = 1 / (2 : ℝ)^n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have hexpm : (2 : ℝ)^(-(m : ℝ)) = 1 / (2 : ℝ)^m := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have hexpslack : (2 : ℝ)^(-(n : ℝ)-2) = 1 / (4 * (2 : ℝ)^n) := by
    rw [Real.rpow_sub (by norm_num), hexpn]
    norm_num
    ring
  rw [hexpslack] at hδ
  rw [hexpm, hexpn]
  have hslack : 1 / (4 * (2 : ℝ)^n) + 1 / (2 * (2 : ℝ)^n) ≤ 1 / (2 : ℝ)^n := by
    field_simp
    nlinarith [hnpos]
  calc
    δ + (m : ℝ)^2 * (1 / (2 : ℝ)^m) = δ + (m : ℝ)^2 / (2 : ℝ)^m := by ring
    _ ≤ 1 / (4 * (2 : ℝ)^n) + 1 / (2 * (2 : ℝ)^n) := add_le_add hδ htail
    _ ≤ 1 / (2 : ℝ)^n := hslack

end GenericGroupWE.Main

-- Exact source with hygienic private names: WitnessEncryption.Correctness



namespace GenericGroupWE.Main.CorrectnessProof
open scoped BigOperators

lemma certificate_coefficients_ne_zero {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (hw : w.Valid) : w.coefficients ≠ 0 := by
  intro h
  have he := hw.1
  rw [h] at he
  have hz : B.combination (0 : Fin B.k → ZMod p.val) = 0 := by simp [MatrixBundle.combination]
  exact hw.2.1 (he.symm.trans hz)

lemma certificate_right_has_one {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (hw : w.Valid) : ∃ i, w.right i = 1 := by
  have hn : w.right ≠ 0 := by
    intro h
    apply hw.2.1
    ext i j
    simp [Matrix.vecMulVec, h]
  obtain ⟨i,hi⟩ : ∃ i, w.right i ≠ 0 := by simpa [funext_iff] using hn
  exact ⟨i,(hw.2.2 i).resolve_left hi⟩

lemma short_multiplier {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (hw : w.Valid) (r : Fin m → Fin m) :
    ∃ q : Fin (m*m),
      (∑ i, w.right i * (((r i).val+1 : ℕ) : ZMod p.val)) =
        ((q.val+1 : ℕ) : ZMod p.val) := by
  classical
  let M : ℕ := ∑ i : Fin m, if w.right i = 1 then (r i).val+1 else 0
  obtain ⟨i,hi⟩ := certificate_right_has_one w hw
  have hMlow : 1 ≤ M := by
    have hh : (if w.right i = 1 then (r i).val+1 else 0) ≤
        ∑ j : Fin m, if w.right j = 1 then (r j).val+1 else 0 :=
      Finset.single_le_sum
        (fun (j : Fin m) _ => Nat.zero_le (if w.right j = 1 then (r j).val+1 else 0))
        (Finset.mem_univ i)
    change (if w.right i = 1 then (r i).val+1 else 0) ≤ M at hh
    rw [if_pos hi] at hh
    omega
  have hMhigh : M ≤ m*m := by
    calc
      M ≤ ∑ _i : Fin m, m := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · exact (r j).isLt
        · exact Nat.zero_le _
      _ = _ := by simp
  have hcast : (M : ZMod p.val) = ∑ i, w.right i * (((r i).val+1 : ℕ) : ZMod p.val) := by
    dsimp [M]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rcases hw.2.2 j with h | h <;> simp [h]
  refine ⟨⟨M-1, by omega⟩, ?_⟩
  rw [← hcast, show M-1+1=M by omega]

lemma bilinear_combination {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (a : Fin B.k → ZMod p.val) (s r : Fin m → ZMod p.val) :
    (∑ j, a j * ∑ i : Fin m, ∑ l : Fin m, s i * B.matrices j i l * r l) =
      ∑ i, (B.combination a).mulVec r i * s i := by
  classical
  simp only [MatrixBundle.combination, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rank_one_pairing {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (hw : w.Valid) (s r : Fin m → ZMod p.val) :
    (∑ j, w.coefficients j * ∑ i : Fin m, ∑ l : Fin m, s i * B.matrices j i l * r l) =
      (∑ i, w.left i*s i) * (∑ l, w.right l*r l) := by
  rw [bilinear_combination, hw.1, Matrix.vecMulVec_mulVec]
  simp only [Pi.smul_apply, op_smul_eq_smul, smul_eq_mul, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end GenericGroupWE.Main.CorrectnessProof


namespace GenericGroupWE.Main.CorrectnessProbability
open scoped BigOperators

lemma probability_map {ι α : Type*} (law : PMF ι) (f : ι → α) (event : α → Prop) :
    probability (law.map f) event = probability law (fun i => event (f i)) := by
  unfold probability
  rw [PMF.toOuterMeasure_map_apply]
  rfl

private lemma Correctness__event_finite {ι : Type*} (law : PMF ι) (E : Set ι) : law.toOuterMeasure E ≠ ⊤ := by
  have hu : law.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa using law.tsum_coe
  have hle : law.toOuterMeasure E ≤ 1 := by
    rw [← hu]
    exact law.toOuterMeasure.mono (Set.subset_univ _)
  exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)

lemma probability_bind_le {ι α : Type*} (law : PMF ι) (F : ι → PMF α) (event : α → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i, probability (F i) event ≤ δ) :
    probability (law.bind F) event ≤ δ := by
  have hpoint : ∀ i, (F i).toOuterMeasure {a | event a} ≤ ENNReal.ofReal δ := by
    intro i
    calc
      _ = ENNReal.ofReal (((F i).toOuterMeasure {a | event a}).toReal) :=
        (ENNReal.ofReal_toReal (Correctness__event_finite _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hF i)
  have houter : (law.bind F).toOuterMeasure {a | event a} ≤ ENNReal.ofReal δ := by
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' i, law i * ENNReal.ofReal δ := by
        apply ENNReal.tsum_le_tsum
        intro i
        exact mul_le_mul_right (hpoint i) (law i)
      _ = _ := by rw [ENNReal.tsum_mul_right, law.tsum_coe, one_mul]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top houter
  simpa only [probability, ENNReal.toReal_ofReal hδ] using hreal

lemma uniform_all_slices_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] (event : ι × κ → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i, probability (PMF.uniformOfFintype κ) (fun j => event (i,j)) ≤ δ) :
    probability (PMF.uniformOfFintype (ι × κ)) event ≤ δ := by
  have hh := FixedTestProof.uniform_condition_bound event (fun _ => False) δ hδ (fun i _ => h i)
  simpa only [FixedTestProof.uniform_probability_const, if_false, zero_add] using hh

lemma uniform_union_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ℕ) (event : Fin L → ι → Prop) :
    probability (PMF.uniformOfFintype ι) (fun x => ∃ q, event q x) ≤
      ∑ q, probability (PMF.uniformOfFintype ι) (event q) := by
  classical
  rw [FixedTestProof.uniform_probability_sum]
  simp_rw [FixedTestProof.uniform_probability_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ q, event q x
  · obtain ⟨q,hq⟩ := hex
    rw [if_pos (show ∃ q, event q x from ⟨q,hq⟩)]
    have hnonneg : ∀ i : Fin L, 0 ≤ (if event i x then (1 : ℝ) else 0) := by
      intro i
      split_ifs <;> norm_num
    have hh : (if event q x then (1 : ℝ) else 0) ≤ ∑ q, if event q x then (1 : ℝ) else 0 :=
      Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ q)
    simpa only [if_pos hq] using hh
  · rw [if_neg hex]
    exact Finset.sum_nonneg (fun q _ => by split_ifs <;> norm_num)

lemma uniform_linear_list_collision (p : PrimeOrder) (k L : ℕ)
    (a : Fin k → ZMod p.val) (ha : a ≠ 0) (z : Fin L → ZMod p.val) :
    probability (PMF.uniformOfFintype (Fin k → ZMod p.val))
      (fun t => ∃ q, (∑ j, a j*t j) = z q) ≤ (L : ℝ)/(p.val : ℝ) := by
  classical
  calc
    _ ≤ ∑ q : Fin L, probability (PMF.uniformOfFintype (Fin k → ZMod p.val))
        (fun t => (∑ j, a j*t j) = z q) := uniform_union_bound L _
    _ ≤ ∑ _q : Fin L, (p.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro q _
      have h := uniform_affine_test_bound p (Fin k) (-(z q)) a (fun hh => ha hh.2)
      have heq : (fun t : Fin k → ZMod p.val => (∑ j, a j*t j) = z q) =
          (fun t => -(z q) + ∑ j, a j*t j = 0) := by
        funext t
        apply propext
        constructor <;> intro ht <;> linear_combination ht
      rw [heq]
      exact h
    _ = _ := by simp [div_eq_mul_inv]

end GenericGroupWE.Main.CorrectnessProbability

namespace GenericGroupWE.Main
open scoped BigOperators

namespace CorrectnessProof

lemma honest_false_decryption {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (w : RankOneCertificate B) (hw : w.Valid) (σ : Encoding p.val)
    (s : Fin m → ZMod p.val) (r : Fin m → Fin m) (t : Fin B.k → ZMod p.val) :
    schemeDecryption w (coordinateCiphertext B σ s (fun i => (r i).val+1) t false) = some false := by
  classical
  obtain ⟨q,hq⟩ := short_multiplier w hw r
  have hZ := rank_one_pairing w hw s (fun i => (((r i).val+1 : ℕ) : ZMod p.val))
  have hE : ∃ q : Fin (m*m),
      (∑ j, w.coefficients j * ∑ i : Fin m, ∑ l : Fin m,
        s i * B.matrices j i l * (((r l).val+1 : ℕ) : ZMod p.val)) =
          ((q.val+1 : ℕ) : ZMod p.val)*(∑ i, w.left i*s i) := by
    refine ⟨q, ?_⟩
    rw [hZ, hq]
    ring
  rw [honest_decryption_identity]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [hE, not_true_eq_false, decide_false]

lemma ideal_failure_bound {m : ℕ} {p : PrimeOrder} {B : MatrixBundle m p}
    (hm : 0 < m) (w : RankOneCertificate B) (hw : w.Valid) (message : Bool) :
    probability (idealEncryption B hm message) (fun C => schemeDecryption w C ≠ some message) ≤
      (m : ℝ)^2/(p.val : ℝ) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  have hδ : 0 ≤ (m : ℝ)^2/(p.val : ℝ) := by positivity
  unfold idealEncryption
  apply CorrectnessProbability.probability_bind_le _ _ _ _ hδ
  intro σ
  rw [CorrectnessProbability.probability_map]
  cases message with
  | false =>
    have hevent : (fun z : (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin B.k → ZMod p.val) =>
        schemeDecryption w (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 false) ≠ some false) =
        (fun _ => False) := by
      funext z
      apply propext
      rw [honest_false_decryption w hw]
      simp
    rw [hevent]
    simpa [probability] using hδ
  | true =>
    have hevent : (fun z : (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin B.k → ZMod p.val) =>
        schemeDecryption w (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 true) ≠ some true) =
        (fun z => ∃ q : Fin (m*m), (∑ j, w.coefficients j*z.2.2 j) =
          ((q.val+1 : ℕ) : ZMod p.val)*(∑ i, w.left i*z.1 i)) := by
      funext z
      apply propext
      rw [honest_decryption_identity]
      simp only [↓reduceIte]
      by_cases he : ∃ q : Fin (m*m), (∑ j, w.coefficients j*z.2.2 j) =
          ((q.val+1 : ℕ) : ZMod p.val)*(∑ i, w.left i*z.1 i) <;> simp [he]
    rw [hevent]
    unfold exactCoordinates
    apply CorrectnessProbability.uniform_all_slices_bound _ _ hδ
    intro s
    apply CorrectnessProbability.uniform_all_slices_bound _ _ hδ
    intro r
    have h := CorrectnessProbability.uniform_linear_list_collision p B.k (m*m) w.coefficients
      (certificate_coefficients_ne_zero w hw)
      (fun q => ((q.val+1 : ℕ) : ZMod p.val)*(∑ i, w.left i*s i))
    simpa only [Nat.cast_mul, pow_two] using h

end CorrectnessProof

end GenericGroupWE.Main



namespace GenericGroupWE.Main
open scoped BigOperators

theorem prop_3_3 (n m : ℕ) (hn : 2 ≤ n) (hm : 16*n ≤ m) (p : PrimeOrder)
    (hp : 2^m ≤ p.val) (B : MatrixBundle m p) (w : RankOneCertificate B)
    (hw : w.Valid) (message : Bool) :
    probability (boundedEncryption B n message) (fun C => schemeDecryption w C ≠ some message) ≤
      samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ∧
    samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ≤ (2 : ℝ)^(-(n : ℝ)) := by
  have hm0 : 0 < m := by omega
  have hsampling := bounded_sampling_distribution m hm0 p B n
  constructor
  · have htransfer := bounded_encryption_event_transfer m hm0 p B n message
      (fun C => schemeDecryption w C ≠ some message)
    have hideal := CorrectnessProof.ideal_failure_bound hm0 w hw message
    have hpow : (0 : ℝ) < (2 : ℝ)^m := by positivity
    have hp' : (2 : ℝ)^m ≤ p.val := by exact_mod_cast hp
    have hinv : (p.val : ℝ)⁻¹ ≤ ((2 : ℝ)^m)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hpow hp'
    have htail : (m : ℝ)^2/(p.val : ℝ) ≤ (m : ℝ)^2*(2 : ℝ)^(-(m : ℝ)) := by
      calc
        _ = (m : ℝ)^2*(p.val : ℝ)⁻¹ := div_eq_mul_inv _ _
        _ ≤ (m : ℝ)^2*((2 : ℝ)^m)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
        _ = _ := by rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact htransfer.trans (add_le_add le_rfl (hideal.trans htail))
  · exact correctness_error_bound n m hn hm (samplingFailure B n) hsampling.1

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∀ (n m : ℕ) (hn : 2 ≤ n) (hm : 16*n ≤ m) (p : PrimeOrder)
    (hp : 2^m ≤ p.val) (B : MatrixBundle m p) (w : RankOneCertificate B)
    (hw : w.Valid) (message : Bool),
probability (boundedEncryption B n message) (fun C => schemeDecryption w C ≠ some message) ≤
      samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ∧
    samplingFailure B n + (m : ℝ)^2 * (2 : ℝ)^(-(m : ℝ)) ≤ (2 : ℝ)^(-(n : ℝ)) :=
  @GenericGroupWE.Main.prop_3_3
