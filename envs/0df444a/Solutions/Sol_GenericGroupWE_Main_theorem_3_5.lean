-- Prove2me | solution 1 for GenericGroupWE.Main.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vigyan
-- created : 2026-11-15T18:46:43.407232+00:00
-- url     : https://prove2.me/submissions/4a713457-8826-40bc-b48c-44a368dd0bee

import Mathlib
import Definitions.Def_GenericGroupWE_Main_Scheme

set_option maxHeartbeats 2000000

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.Runtime.Binary.Value

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

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.EncodingCompletions

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

lemma label_space_square (p : ℕ) : p^2 ≤ 2^labelLength p := by
  unfold labelLength
  rw [Nat.mul_comm 2, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) p) 2

/-- Provisional proof-side predicate: complete physical injections respecting
an already revealed revealed injection and all failed valid-width guesses. -/
def Completion {α β : Type*} (known : Finset α) (revealed : known ↪ β) (excluded : Finset β) :=
  {σ : α ↪ β // (∀ a : known, σ a.val = revealed a) ∧ ∀ a : α, σ a ∉ excluded}

abbrev Unknown {α : Type*} (known : Finset α) := {a : α // a ∉ known}

abbrev Available {α β : Type*} (known : Finset α) (revealed : known ↪ β) (excluded : Finset β) :=
  {b : β // b ∉ excluded ∧ b ∉ Set.range revealed}

noncomputable def completionToFree {α β : Type*} [DecidableEq α]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (σ : Completion known revealed excluded) : Unknown known ↪ Available known revealed excluded := by
  classical
  refine ⟨fun a => ⟨σ.val a.val, σ.property.2 a.val, ?_⟩, ?_⟩
  · rintro ⟨d,hd⟩
    have ha : a.val = d.val := σ.val.injective (by rw [σ.property.1 d]; exact hd.symm)
    exact a.property (ha.symm ▸ d.property)
  · intro a b hab
    apply Subtype.ext
    exact σ.val.injective (congrArg Subtype.val hab)

noncomputable def extendFree {α β : Type*} [DecidableEq α]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (free : Unknown known ↪ Available known revealed excluded) : α ↪ β := by
  classical
  refine ⟨fun a => if h : a ∈ known then revealed ⟨a,h⟩ else (free ⟨a,h⟩).val, ?_⟩
  intro a b hab
  by_cases ha : a ∈ known <;> by_cases hb : b ∈ known
  · simp only [dif_pos ha, dif_pos hb] at hab
    exact congrArg Subtype.val (revealed.injective hab)
  · simp only [dif_pos ha, dif_neg hb] at hab
    exact False.elim ((free ⟨b,hb⟩).property.2 ⟨⟨a,ha⟩,hab⟩)
  · simp only [dif_neg ha, dif_pos hb] at hab
    exact False.elim ((free ⟨a,ha⟩).property.2 ⟨⟨b,hb⟩,hab.symm⟩)
  · simp only [dif_neg ha, dif_neg hb] at hab
    exact congrArg Subtype.val (free.injective (Subtype.ext hab))

noncomputable def freeToCompletion {α β : Type*} [DecidableEq α]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (hpartial : ∀ a, revealed a ∉ excluded)
    (free : Unknown known ↪ Available known revealed excluded) : Completion known revealed excluded := by
  classical
  refine ⟨extendFree known revealed excluded free, ?_, ?_⟩
  · intro a
    change (if h : a.val ∈ known then revealed ⟨a.val,h⟩ else (free ⟨a.val,h⟩).val) = revealed a
    rw [dif_pos a.property]
  · intro a
    by_cases ha : a ∈ known
    · change (if h : a ∈ known then revealed ⟨a,h⟩ else (free ⟨a,h⟩).val) ∉ excluded
      rw [dif_pos ha]
      exact hpartial ⟨a,ha⟩
    · change (if h : a ∈ known then revealed ⟨a,h⟩ else (free ⟨a,h⟩).val) ∉ excluded
      rw [dif_neg ha]
      exact (free ⟨a,ha⟩).property.1

/-- Every conditioned physical encoding is exactly an injection of the unknown
field elements into the as-yet unused and unexcluded code labels. -/
noncomputable def completionEquiv {α β : Type*} [DecidableEq α]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (hpartial : ∀ a, revealed a ∉ excluded) :
    Completion known revealed excluded ≃ (Unknown known ↪ Available known revealed excluded) where
  toFun := completionToFree known revealed excluded
  invFun := freeToCompletion known revealed excluded hpartial
  left_inv σ := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro a
    change (if h : a ∈ known then revealed ⟨a,h⟩ else
      ((completionToFree known revealed excluded σ) ⟨a,h⟩).val) = σ.val a
    by_cases ha : a ∈ known
    · rw [dif_pos ha]
      exact (σ.property.1 ⟨a,ha⟩).symm
    · rw [dif_neg ha]
      rfl
  right_inv free := by
    apply Function.Embedding.ext
    intro a
    apply Subtype.ext
    change (if h : a.val ∈ known then revealed ⟨a.val,h⟩ else (free ⟨a.val,h⟩).val) = (free a).val
    rw [dif_neg a.property]

lemma unknown_card {α : Type*} [Fintype α] [DecidableEq α] (known : Finset α) :
    Nat.card (Unknown known) = Nat.card α-known.card := by
  classical
  have h := Fintype.card_subtype_compl (fun a : α => a ∈ known)
  simpa only [Unknown, Nat.card_eq_fintype_card, Fintype.card_coe] using h

lemma available_card {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (hpartial : ∀ a, revealed a ∉ excluded) :
    Nat.card (Available known revealed excluded) = Nat.card β-known.card-excluded.card := by
  classical
  let used : Finset β := Finset.univ.image revealed
  let both : Finset β := used ∪ excluded
  have hmem (b : β) : b ∈ used ↔ b ∈ Set.range revealed := by simp [used]
  have hused : used.card = known.card := by
    dsimp [used]
    rw [Finset.card_image_of_injective _ revealed.injective]
    simp
  have hdis : Disjoint used excluded := by
    apply Finset.disjoint_left.mpr
    intro b hb he
    obtain ⟨a,ha⟩ := (hmem b).mp hb
    subst b
    exact hpartial a he
  have hboth : both.card = known.card+excluded.card := by
    dsimp [both]
    rw [Finset.card_union_of_disjoint hdis, hused]
  let e : Available known revealed excluded ≃ {b : β // b ∉ both} :=
    { toFun := fun b => ⟨b.val, by
        simp only [both, Finset.mem_union, not_or]
        exact ⟨fun h => b.property.2 ((hmem _).mp h), b.property.1⟩⟩
      invFun := fun b => ⟨b.val, by
        have hh : b.val ∉ used ∧ b.val ∉ excluded := by
          simpa only [both, Finset.mem_union, not_or] using b.property
        exact ⟨hh.2, fun h => hh.1 ((hmem _).mpr h)⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hc : Nat.card {b : β // b ∉ both} = Nat.card β-both.card := by
    have h := Fintype.card_subtype_compl (fun b : β => b ∈ both)
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
  rw [Nat.card_congr e, hc, hboth, Nat.sub_add_eq]

lemma completion_card {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (hpartial : ∀ a, revealed a ∉ excluded) :
    Nat.card (Completion known revealed excluded) =
      (Nat.card β-known.card-excluded.card).descFactorial (Nat.card α-known.card) := by
  classical
  rw [Nat.card_congr (completionEquiv known revealed excluded hpartial)]
  have h : Nat.card (Unknown known ↪ Available known revealed excluded) =
      (Nat.card (Available known revealed excluded)).descFactorial (Nat.card (Unknown known)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  rw [h, available_card known revealed excluded hpartial, unknown_card known]


end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.EmbeddingReveal

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

lemma uniform_event_card {ι : Type*} [Fintype ι] [Nonempty ι] (event : ι → Prop) :
    probability (PMF.uniformOfFintype ι) event =
      (Nat.card {x : ι | event x} : ℝ)/(Nat.card ι : ℝ) := by
  classical
  unfold probability
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ← Nat.card_eq_fintype_card]

lemma embedding_fibres_equinumerous {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (b c : β) :
    Nat.card {σ : α ↪ β | σ a = b} = Nat.card {σ : α ↪ β | σ a = c} := by
  classical
  let e : (α ↪ β) ≃ (α ↪ β) := Equiv.embeddingCongr (Equiv.refl α) (Equiv.swap b c)
  apply Nat.card_congr
  apply Equiv.subtypeEquiv e
  intro σ
  change (σ a = b) ↔ Equiv.swap b c (σ a) = c
  rw [Equiv.apply_eq_iff_eq_symm_apply]
  simp

lemma embedding_fibre_total {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) :
    Nat.card (α ↪ β) = Nat.card β * Nat.card {σ : α ↪ β | σ a = b} := by
  classical
  let e : (Σ c : β, {σ : α ↪ β | σ a = c}) ≃ (α ↪ β) :=
    { toFun := fun z => z.2.val
      invFun := fun σ => ⟨σ a,σ,rfl⟩
      left_inv := by
        rintro ⟨c,σ,hσ⟩
        change σ a = c at hσ
        cases hσ
        rfl
      right_inv _ := rfl }
  calc
    Nat.card (α ↪ β) = Nat.card (Σ c : β, {σ : α ↪ β | σ a = c}) := Nat.card_congr e.symm
    _ = ∑ c : β, Nat.card {σ : α ↪ β | σ a = c} := Nat.card_sigma
    _ = ∑ _c : β, Nat.card {σ : α ↪ β | σ a = b} := by
      apply Finset.sum_congr rfl
      intro c _
      exact embedding_fibres_equinumerous a c b
    _ = _ := by simp [Nat.card_eq_fintype_card]

lemma uniform_embedding_forward {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty (α ↪ β)] (a : α) (b : β) :
    probability (PMF.uniformOfFintype (α ↪ β)) (fun σ => σ a = b) = 1/(Nat.card β : ℝ) := by
  classical
  have htotal := embedding_fibre_total a b
  have hE : 0 < Nat.card (α ↪ β) := Nat.card_pos
  have hF : Nat.card {σ : α ↪ β | σ a = b} ≠ 0 := by
    intro h
    rw [h,mul_zero] at htotal
    omega
  have hN : Nat.card β ≠ 0 := by
    intro h
    rw [h,zero_mul] at htotal
    omega
  have hcast : (Nat.card (α ↪ β) : ℝ) =
      (Nat.card β : ℝ)*(Nat.card {σ : α ↪ β | σ a = b} : ℝ) := by exact_mod_cast htotal
  rw [uniform_event_card, hcast]
  field_simp [Nat.cast_ne_zero.mpr hF, Nat.cast_ne_zero.mpr hN]

lemma uniform_event_sum {ι : Type*} [Fintype ι] [Nonempty ι]
    (event : ι → Prop) [DecidablePred event] :
    probability (PMF.uniformOfFintype ι) event =
      (∑ x : ι, if event x then (1 : ℝ) else 0)/(Nat.card ι : ℝ) := by
  classical
  rw [uniform_event_card]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Set.mem_ofPred_eq]

lemma uniform_embedding_inverse {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty (α ↪ β)] (b : β) :
    probability (PMF.uniformOfFintype (α ↪ β)) (fun σ => b ∈ Set.range σ) =
      (Nat.card α : ℝ)/(Nat.card β : ℝ) := by
  classical
  have hpoint : ∀ σ : α ↪ β,
      (if b ∈ Set.range σ then (1 : ℝ) else 0) = ∑ a : α, if σ a=b then (1 : ℝ) else 0 := by
    intro σ
    by_cases hb : b ∈ Set.range σ
    · obtain ⟨a,ha⟩ := hb
      rw [if_pos (show b ∈ Set.range σ from ⟨a,ha⟩)]
      have hs : (∑ a' : α, if σ a'=b then (1 : ℝ) else 0) =
          (if σ a=b then (1 : ℝ) else 0) := by
        apply Fintype.sum_eq_single a
        intro a' hne
        exact if_neg (fun he => hne (σ.injective (he.trans ha.symm)))
      rw [hs,if_pos ha]
    · rw [if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro a _
      exact if_neg (fun h => hb ⟨a,h⟩)
  rw [uniform_event_sum]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  calc
    (∑ a : α, ∑ σ : α ↪ β, if σ a=b then (1 : ℝ) else 0)/(Nat.card (α ↪ β) : ℝ) =
        ∑ a : α, probability (PMF.uniformOfFintype (α ↪ β)) (fun σ => σ a=b) := by
      simp only [uniform_event_sum, Finset.sum_div]
    _ = ∑ _a : α, 1/(Nat.card β : ℝ) := by
      apply Finset.sum_congr rfl
      intro a _
      exact uniform_embedding_forward a b
    _ = _ := by simp [Nat.card_eq_fintype_card,div_eq_mul_inv]

theorem uniform_embedding_reveal_counts :
    ∀ (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
      [Nonempty (α ↪ β)],
      (∀ (a : α) (b : β), probability (PMF.uniformOfFintype (α ↪ β))
        (fun σ => σ a=b) = 1/(Nat.card β : ℝ)) ∧
      (∀ b : β, probability (PMF.uniformOfFintype (α ↪ β))
        (fun σ => b ∈ Set.range σ) = (Nat.card α : ℝ)/(Nat.card β : ℝ)) := by
  intro α β _ _ _ _ _
  exact ⟨uniform_embedding_forward, uniform_embedding_inverse⟩


end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecuritySimulator

namespace GenericGroupWE.Main.GenericSecurityProof

abbrev Coefficient (p : PrimeOrder) (m k : ℕ) :=
  ZMod p.val × (Fin m → ZMod p.val) × (Fin k → ZMod p.val)

abbrev Code (p : PrimeOrder) := Fin (2^labelLength p.val)

def codeBits (p : PrimeOrder) (b : Code p) : Bits := fixedBits (labelLength p.val) b.val

/-- Total parsing; the second check is automatic for valid-width bit strings,
but is explicit here so this proof-side data definition has no proof holes. -/
def readCode (p : PrimeOrder) (x : Bits) : Option (Code p) :=
  if x.length = labelLength p.val then
    if h : bitsNat x < 2^labelLength p.val then some ⟨bitsNat x,h⟩ else none
  else none

/-- Raw finite lazy dictionary. The validity invariant is proved separately;
exhaustion has an explicit total fallback instead of a global formal embedding. -/
structure SimulatorState (p : PrimeOrder) (m k : ℕ) where
  entries : List (Coefficient p m k × Code p)
  excluded : Finset (Code p)
  dead : Bool

noncomputable def lookupExpr {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (c : Coefficient p m k) : Option (Code p) := by
  classical
  exact (st.entries.find? (fun e => decide (e.1=c))).map Prod.snd

noncomputable def lookupCode {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (b : Code p) : Option (Coefficient p m k) := by
  classical
  exact (st.entries.find? (fun e => decide (e.2=b))).map Prod.fst

noncomputable def lookupOperand {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : Option (Coefficient p m k) :=
  (readCode p x).bind (lookupCode st)

def freshCodes {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k) : Finset (Code p) :=
  Finset.univ.filter (fun b => b ∉ (st.entries.map Prod.snd).toFinset ∧ b ∉ st.excluded)

noncomputable def allocate {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (c : Coefficient p m k) :
    PMF (Option (Code p) × SimulatorState p m k) := by
  classical
  exact if st.dead then pure (none,st) else
    match lookupExpr st c with
    | some b => pure (some b,st)
    | none => if h : (freshCodes st).Nonempty then
        (PMF.uniformOfFinset (freshCodes st) h).map fun b =>
          (some b,{st with entries := st.entries ++ [(c,b)]})
      else pure (none,{st with dead := true})

noncomputable def excludeOperand {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : SimulatorState p m k := by
  classical
  exact match readCode p x with
    | none => st
    | some b => if (lookupCode st b).isNone then {st with excluded := insert b st.excluded} else st

/-- Both unknown operands are excluded, even when the other one already makes
the real oracle reply invalid. A hit by either operand is counted as bad. -/
noncomputable def simulatorStep {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits) :
    PMF (Option Bits × SimulatorState p m k) := by
  classical
  exact if st.dead then pure (none,st) else
    let next := excludeOperand (excludeOperand st x) y
    match lookupOperand st x, lookupOperand st y with
    | some a, some b => (allocate next (if subtract then a-b else a+b)).map fun result =>
        (result.1.map (codeBits p), result.2)
    | _, _ => pure (none,next)

def oneCoefficient (p : PrimeOrder) (m k : ℕ) : Coefficient p m k := (1,0,0)
def sCoefficient (p : PrimeOrder) (m k : ℕ) (i : Fin m) : Coefficient p m k :=
  (0,Pi.single i 1,0)
def zCoefficient (p : PrimeOrder) (m k : ℕ) (j : Fin k) : Coefficient p m k :=
  (0,0,Pi.single j 1)

def initialForms (p : PrimeOrder) (m k : ℕ) : List (Coefficient p m k) :=
  [oneCoefficient p m k] ++ List.ofFn (sCoefficient p m k) ++ List.ofFn (zCoefficient p m k)

noncomputable def allocateForms {p : PrimeOrder} {m k : ℕ} :
    List (Coefficient p m k) → SimulatorState p m k → PMF (SimulatorState p m k)
  | [],st => pure st
  | c::cs,st => (allocate st c).bind fun result => allocateForms cs result.2

noncomputable def simulatorPublic {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k) : Bits :=
  let encode := fun c => ((lookupExpr st c).map (codeBits p)).getD []
  let g := encode (oneCoefficient p m k)
  let xs := List.ofFn fun i => encode (sCoefficient p m k i)
  let ys := List.ofFn fun j => encode (zCoefficient p m k j)
  pack [true :: pack [p.val.bits,g], replyBits (some (pack [g,pack xs,pack ys]))]

noncomputable def simulatorTree {p : PrimeOrder} {m k : ℕ}
    (q : ℕ) (tree : QueryTree q) (st : SimulatorState p m k) :
    PMF (Bool × SimulatorState p m k) :=
  if st.dead then pure (false,st) else
    match tree with
    | .halt bit => pure (bit,st)
    | .query subtract x y continuation =>
      (simulatorStep st subtract x y).bind fun result =>
        simulatorTree _ (continuation result.1) result.2
termination_by q

/-- Complete proof-side simulator law. It has no latent s/r/t or message input;
it samples labels only for the finite visited dictionary. -/
noncomputable def simulator (p : PrimeOrder) (m k Q : ℕ) (A : Adversary Q) : PMF Bool :=
  (allocateForms (initialForms p m k) (⟨[],∅,false⟩ : SimulatorState p m k)).bind fun st =>
    (A (simulatorPublic st)).bind fun tree => (simulatorTree Q tree st).map Prod.fst

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.FiniteUniformConditioning

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

/-- Total finite conditional kernel, with a harmless fallback on empty fibres. -/
noncomputable def fibreKernel {ι κ : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → κ) (o : κ) : PMF ι := by
  classical
  exact if h : Nonempty {x : ι // f x=o} then
    (@PMF.uniformOfFintype {x : ι // f x=o} inferInstance h).map Subtype.val
  else PMF.uniformOfFintype ι

lemma uniform_map_mass {ι κ : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → κ) (o : κ) :
    ((PMF.uniformOfFintype ι).map f) o =
      (Nat.card {x : ι // f x=o} : ENNReal)/(Nat.card ι : ENNReal) := by
  classical
  have hcard : (Finset.univ.filter (fun x : ι => o=f x)).card = Nat.card {x : ι // f x=o} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  simp only [Nat.card_eq_fintype_card, div_eq_mul_inv]

lemma fibreKernel_apply {ι κ : Type*} [Fintype ι] [Nonempty ι] [DecidableEq κ]
    (f : ι → κ) (o : κ) (h : Nonempty {x : ι // f x=o}) (x : ι) :
    fibreKernel f o x = if f x=o then (Nat.card {y : ι // f y=o} : ENNReal)⁻¹ else 0 := by
  classical
  unfold fibreKernel
  rw [dif_pos h, PMF.map_apply]
  by_cases hx : f x=o
  · have heq (y : {y : ι // f y=o}) : x=y.val ↔ y=⟨x,hx⟩ := by
      constructor
      · intro hy
        exact Subtype.ext hy.symm
      · rintro rfl
        rfl
    simp_rw [heq]
    simp only [tsum_ite_eq, PMF.uniformOfFintype_apply, if_pos hx, ← Nat.card_eq_fintype_card]
  · rw [if_neg hx]
    apply ENNReal.tsum_eq_zero.mpr
    intro y
    apply if_neg
    intro hy
    exact hx (hy ▸ y.property)

theorem uniform_fibre_recombine {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) :
    ((PMF.uniformOfFintype ι).map f).bind (fibreKernel f) = PMF.uniformOfFintype ι := by
  classical
  apply PMF.ext
  intro x
  rw [PMF.bind_apply, PMF.uniformOfFintype_apply]
  have hzero : ∀ o : κ, o ≠ f x →
      ((PMF.uniformOfFintype ι).map f) o * fibreKernel f o x = 0 := by
    intro o ho
    by_cases hn : Nonempty {y : ι // f y=o}
    · rw [fibreKernel_apply f o hn x, if_neg (Ne.symm ho), mul_zero]
    · letI : IsEmpty {y : ι // f y=o} := not_nonempty_iff.mp hn
      rw [uniform_map_mass]
      simp
  rw [tsum_eq_single (f x) hzero]
  letI : Nonempty {y : ι // f y=f x} := ⟨⟨x,rfl⟩⟩
  have hF : (Nat.card {y : ι // f y=f x} : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := {y : ι // f y=f x})).ne'
  rw [uniform_map_mass, fibreKernel_apply f (f x) inferInstance x, if_pos rfl]
  rw [← Nat.card_eq_fintype_card]
  calc
    (Nat.card {y : ι // f y=f x} : ENNReal)/(Nat.card ι : ENNReal) *
        (Nat.card {y : ι // f y=f x} : ENNReal)⁻¹ =
      (Nat.card ι : ENNReal)⁻¹ * ((Nat.card {y : ι // f y=f x} : ENNReal) *
        (Nat.card {y : ι // f y=f x} : ENNReal)⁻¹) := by
      simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hF (by finiteness), mul_one]

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.PhysicalEncoding

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators


lemma uniform_equiv_map {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (e : ι ≃ κ) : (PMF.uniformOfFintype ι).map e = PMF.uniformOfFintype κ := by
  classical
  apply PMF.ext
  intro x
  rw [PMF.map_apply]
  have heq (y : ι) : x=e y ↔ y=e.symm x := by
    constructor
    · intro h
      simpa only [Equiv.symm_apply_apply] using (congrArg e.symm h).symm
    · rintro rfl
      simp
  simp_rw [heq]
  simp only [tsum_ite_eq, PMF.uniformOfFintype_apply, Fintype.card_congr e]

lemma uniform_embedding_forward_map {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty (α ↪ β)] [Nonempty β] (a : α) :
    (PMF.uniformOfFintype (α ↪ β)).map (fun σ => σ a) = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  have heq : ((PMF.uniformOfFintype (α ↪ β)).map (fun σ => σ a)) b =
      (PMF.uniformOfFintype (α ↪ β)).toOuterMeasure {σ | σ a=b} := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    rfl
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ b) (PMF.apply_ne_top _ b)).mp
  rw [heq]
  change probability (PMF.uniformOfFintype (α ↪ β)) (fun σ => σ a=b) = _
  rw [uniform_embedding_forward, PMF.uniformOfFintype_apply]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.card_eq_fintype_card, one_div]



noncomputable def evaluation (p : PrimeOrder) (m k : ℕ)
    (s : Fin m → ZMod p.val) (y : Fin k → ZMod p.val) :
    Coefficient p m k →ₗ[ZMod p.val] ZMod p.val where
  toFun c := c.1 + (∑ i, c.2.1 i*s i) + (∑ j, c.2.2 j*y j)
  map_add' c d := by
    change (c.1+d.1) + (∑ i, (c.2.1 i+d.2.1 i)*s i) +
      (∑ j, (c.2.2 j+d.2.2 j)*y j) = _
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a c := by
    change a*c.1 + (∑ i, (a*c.2.1 i)*s i) + (∑ j, (a*c.2.2 j)*y j) =
      a*(c.1 + (∑ i, c.2.1 i*s i) + (∑ j, c.2.2 j*y j))
    simp only [mul_add, Finset.mul_sum, mul_assoc]

def fieldIndex (p : PrimeOrder) (z : ZMod p.val) : Fin p.val := ⟨z.val,ZMod.val_lt z⟩

def WellFormed {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k) : Prop :=
  (st.entries.map Prod.fst).Nodup ∧ (st.entries.map Prod.snd).Nodup ∧
    Disjoint (st.entries.map Prod.snd).toFinset st.excluded

/-- Explicit relation to a physical finite injection, with all exclusions. -/
def Compatible {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (σ : Encoding p.val) : Prop :=
  (∀ e ∈ st.entries, σ (fieldIndex p (φ e.1)) = e.2) ∧
    ∀ b ∈ st.excluded, b ∉ Set.range σ

abbrev PhysicalCompletion {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) :=
  {σ : Encoding p.val // Compatible φ st σ}

def stepGuess {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k)
    (σ : Encoding p.val) (x y : Bits) : Prop :=
  ∃ b : Code p, (readCode p x=some b ∨ readCode p y=some b) ∧
    lookupCode st b=none ∧ b ∈ Set.range σ

def stepCollision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (subtract : Bool) (x y : Bits) : Prop :=
  ∃ a b : Coefficient p m k, lookupOperand st x=some a ∧ lookupOperand st y=some b ∧
    ∃ e ∈ st.entries, (if subtract then a-b else a+b) ≠ e.1 ∧
      φ (if subtract then a-b else a+b) = φ e.1



noncomputable def physicalEncodingLaw {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) : PMF (Encoding p.val) := by
  classical
  exact (@PMF.uniformOfFintype (PhysicalCompletion φ st) inferInstance h).map Subtype.val

def knownPoints {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) : Finset (Fin p.val) :=
  (st.entries.map (fun e => fieldIndex p (φ e.1))).toFinset

lemma mem_knownPoints {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) (a : Fin p.val) :
    a ∈ knownPoints φ st ↔ ∃ e ∈ st.entries, fieldIndex p (φ e.1)=a := by
  simp only [knownPoints, List.mem_toFinset, List.mem_map]

def witnessReveal {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) : knownPoints φ st ↪ Code p :=
  ⟨fun a => σ₀ a.val, fun a b h => Subtype.ext (σ₀.injective h)⟩

lemma compatible_completion_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) (h₀ : Compatible φ st σ₀) (σ : Encoding p.val) :
    Compatible φ st σ ↔
      (∀ a : knownPoints φ st, σ a.val = witnessReveal φ st σ₀ a) ∧
        ∀ a : Fin p.val, σ a ∉ st.excluded := by
  constructor
  · intro hs
    constructor
    · intro a
      obtain ⟨e,he,hea⟩ := (mem_knownPoints φ st a.val).mp a.property
      change σ a.val = σ₀ a.val
      rw [← hea, hs.1 e he, h₀.1 e he]
    · intro a ha
      exact hs.2 (σ a) ha ⟨a,rfl⟩
  · rintro ⟨hknown,hexcluded⟩
    constructor
    · intro e he
      have ha : fieldIndex p (φ e.1) ∈ knownPoints φ st :=
        (mem_knownPoints φ st _).mpr ⟨e,he,rfl⟩
      exact (hknown ⟨fieldIndex p (φ e.1),ha⟩).trans (h₀.1 e he)
    · intro b hb
      rintro ⟨a,ha⟩
      subst b
      exact hexcluded a hb

noncomputable def physicalCompletionEquiv {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) (h₀ : Compatible φ st σ₀) :
    PhysicalCompletion φ st ≃ Completion (knownPoints φ st) (witnessReveal φ st σ₀) st.excluded where
  toFun σ := ⟨σ.val,(compatible_completion_iff φ st σ₀ h₀ σ.val).mp σ.property⟩
  invFun σ := ⟨σ.val,(compatible_completion_iff φ st σ₀ h₀ σ.val).mpr σ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma witnessReveal_excluded {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) (h₀ : Compatible φ st σ₀) :
    ∀ a : knownPoints φ st, witnessReveal φ st σ₀ a ∉ st.excluded := by
  intro a ha
  exact h₀.2 (σ₀ a.val) ha ⟨a.val,rfl⟩

lemma witnessReveal_range {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) (h₀ : Compatible φ st σ₀) (b : Code p) :
    b ∈ Set.range (witnessReveal φ st σ₀) ↔ b ∈ (st.entries.map Prod.snd).toFinset := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨e,he,hea⟩ := (mem_knownPoints φ st a.val).mp a.property
    change σ₀ a.val = b at ha
    rw [← hea, h₀.1 e he] at ha
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,ha⟩)
  · intro hb
    obtain ⟨e,he,heb⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    have ha : fieldIndex p (φ e.1) ∈ knownPoints φ st :=
      (mem_knownPoints φ st _).mpr ⟨e,he,rfl⟩
    refine ⟨⟨fieldIndex p (φ e.1),ha⟩, ?_⟩
    change σ₀ (fieldIndex p (φ e.1)) = b
    exact (h₀.1 e he).trans heb

lemma fieldIndex_injective (p : PrimeOrder) : Function.Injective (fieldIndex p) := by
  intro x y h
  exact ZMod.val_injective p.val (congrArg Fin.val h)

lemma new_point_unknown {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (c : Coefficient p m k) (hnew : ∀ e ∈ st.entries, φ c ≠ φ e.1) :
    fieldIndex p (φ c) ∉ knownPoints φ st := by
  intro ha
  obtain ⟨e,he,hea⟩ := (mem_knownPoints φ st _).mp ha
  exact hnew e he ((fieldIndex_injective p hea).symm)



lemma uniform_finset_subtype {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) [Nonempty s] :
    (PMF.uniformOfFintype s).map (Subtype.val : s → ι) = PMF.uniformOfFinset s hs := by
  classical
  apply PMF.ext
  intro x
  rw [PMF.map_apply, PMF.uniformOfFinset_apply]
  by_cases hx : x ∈ s
  · have heq (a : s) : x=a.val ↔ a=⟨x,hx⟩ := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · rintro rfl
        rfl
    simp_rw [heq]
    simp only [tsum_ite_eq, PMF.uniformOfFintype_apply, Fintype.card_coe, if_pos hx]
  · rw [if_neg hx]
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    apply if_neg
    intro h
    exact hx (h ▸ a.property)

noncomputable def availableFreshEquiv {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ₀ : Encoding p.val) (h₀ : Compatible φ st σ₀) :
    Available (knownPoints φ st) (witnessReveal φ st σ₀) st.excluded ≃ (freshCodes st) where
  toFun b := ⟨b.val, by
    simp only [freshCodes, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hb => b.property.2 ((witnessReveal_range φ st σ₀ h₀ _).mpr hb), b.property.1⟩⟩
  invFun b := ⟨b.val, by
    have hb : b.val ∉ (st.entries.map Prod.snd).toFinset ∧ b.val ∉ st.excluded := by
      simpa only [freshCodes, Finset.mem_filter, Finset.mem_univ, true_and] using b.property
    exact ⟨hb.2, fun h => hb.1 ((witnessReveal_range φ st σ₀ h₀ _).mp h)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fresh_physical_forward {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (c : Coefficient p m k)
    (hnew : ∀ e ∈ st.entries, φ c ≠ φ e.1) (hfresh : (freshCodes st).Nonempty) :
    (physicalEncodingLaw φ st h).map (fun σ => σ (fieldIndex p (φ c))) =
      PMF.uniformOfFinset (freshCodes st) hfresh := by
  classical
  let σ₀ : PhysicalCompletion φ st := Classical.choice h
  let known := knownPoints φ st
  let revealed := witnessReveal φ st σ₀.val
  let a : Unknown known := ⟨fieldIndex p (φ c),new_point_unknown φ st c hnew⟩
  let e := (physicalCompletionEquiv φ st σ₀.val σ₀.property).trans
    (completionEquiv known revealed st.excluded (witnessReveal_excluded φ st σ₀.val σ₀.property))
  let eA := availableFreshEquiv φ st σ₀.val σ₀.property
  letI : Nonempty (PhysicalCompletion φ st) := h
  letI : Nonempty (Unknown known ↪ Available known revealed st.excluded) := Nonempty.map e h
  letI : Nonempty (Available known revealed st.excluded) := by
    obtain ⟨f⟩ := (inferInstance : Nonempty (Unknown known ↪ Available known revealed st.excluded))
    exact ⟨f a⟩
  letI : Nonempty (freshCodes st) := by
    obtain ⟨b,hb⟩ := hfresh
    exact ⟨⟨b,hb⟩⟩
  calc
    (physicalEncodingLaw φ st h).map (fun σ => σ (fieldIndex p (φ c))) =
        ((PMF.uniformOfFintype (PhysicalCompletion φ st)).map e).map
          (fun f => (f a).val) := by
      unfold physicalEncodingLaw
      rw [PMF.map_comp, PMF.map_comp]
      congr 1
    _ = (PMF.uniformOfFintype (Unknown known ↪ Available known revealed st.excluded)).map
        (fun f => (f a).val) := by rw [uniform_equiv_map e]
    _ = (PMF.uniformOfFintype (Available known revealed st.excluded)).map Subtype.val := by
      have hh := uniform_embedding_forward_map (α := Unknown known)
        (β := Available known revealed st.excluded) a
      have hm := congrArg (fun law : PMF (Available known revealed st.excluded) => law.map Subtype.val) hh
      simpa only [PMF.map_comp, Function.comp_def] using hm
    _ = ((PMF.uniformOfFintype (Available known revealed st.excluded)).map eA).map Subtype.val := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (freshCodes st)).map Subtype.val := by rw [uniform_equiv_map eA]
    _ = _ := uniform_finset_subtype (freshCodes st) hfresh



lemma probability_map_local {ι α : Type*} (law : PMF ι) (f : ι → α) (event : α → Prop) :
    probability (law.map f) event = probability law (fun x => event (f x)) := by
  unfold probability
  rw [PMF.toOuterMeasure_map_apply]
  rfl

lemma completion_free_range {α β : Type*} [DecidableEq α]
    (known : Finset α) (revealed : known ↪ β) (excluded : Finset β)
    (σ : Completion known revealed excluded) (b : Available known revealed excluded) :
    b.val ∈ Set.range σ.val ↔ b ∈ Set.range (completionToFree known revealed excluded σ) := by
  constructor
  · rintro ⟨a,ha⟩
    have hn : a ∉ known := by
      intro hk
      exact b.property.2 ⟨⟨a,hk⟩,(σ.property.1 ⟨a,hk⟩).symm.trans ha⟩
    exact ⟨⟨a,hn⟩,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a.val,congrArg Subtype.val ha⟩

theorem physical_unknown_hit {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (b : Code p)
    (hused : b ∉ (st.entries.map Prod.snd).toFinset) (hexcluded : b ∉ st.excluded) :
    probability (physicalEncodingLaw φ st h) (fun σ => b ∈ Set.range σ) =
      ((p.val-(knownPoints φ st).card : ℕ) : ℝ) /
        ((2^labelLength p.val-(knownPoints φ st).card-st.excluded.card : ℕ) : ℝ) := by
  classical
  let σ₀ : PhysicalCompletion φ st := Classical.choice h
  let known := knownPoints φ st
  let revealed := witnessReveal φ st σ₀.val
  let e := (physicalCompletionEquiv φ st σ₀.val σ₀.property).trans
    (completionEquiv known revealed st.excluded (witnessReveal_excluded φ st σ₀.val σ₀.property))
  let a : Available known revealed st.excluded :=
    ⟨b,hexcluded,fun hb => hused ((witnessReveal_range φ st σ₀.val σ₀.property b).mp hb)⟩
  letI : Nonempty (PhysicalCompletion φ st) := h
  letI : Nonempty (Unknown known ↪ Available known revealed st.excluded) := Nonempty.map e h
  have hh := uniform_embedding_inverse (α := Unknown known)
    (β := Available known revealed st.excluded) a
  rw [unknown_card, available_card known revealed st.excluded
    (witnessReveal_excluded φ st σ₀.val σ₀.property)] at hh
  have ht : probability (physicalEncodingLaw φ st h) (fun σ => b ∈ Set.range σ) =
      probability ((PMF.uniformOfFintype (PhysicalCompletion φ st)).map e)
        (fun f => a ∈ Set.range f) := by
    rw [probability_map_local]
    unfold physicalEncodingLaw
    rw [probability_map_local]
    congr 1
    funext σ
    exact propext (completion_free_range known revealed st.excluded
      ((physicalCompletionEquiv φ st σ₀.val σ₀.property) σ) a)
  rw [ht, uniform_equiv_map e]
  simpa only [Nat.card_fin] using hh


lemma uniform_refinement {ι κ : Type*} [Fintype ι]
    (P Q : ι → Prop) (f : ι → κ) (b : κ)
    (hP : Nonempty {x : ι // P x}) (hQ : Nonempty {x : ι // Q x})
    (hiff : ∀ x, Q x ↔ P x ∧ f x=b) :
    (@fibreKernel {x : ι // P x} κ (by classical exact inferInstance) hP (fun x => f x.val) b).map Subtype.val =
      (@PMF.uniformOfFintype {x : ι // Q x} (by classical exact inferInstance) hQ).map Subtype.val := by
  classical
  letI : Nonempty {x : ι // P x} := hP
  letI : Nonempty {x : ι // Q x} := hQ
  let e : {x : {x : ι // P x} // f x.val=b} ≃ {x : ι // Q x} :=
    { toFun := fun x => ⟨x.val.val,(hiff x.val.val).mpr ⟨x.val.property,x.property⟩⟩
      invFun := fun x => ⟨⟨x.val,((hiff x.val).mp x.property).1⟩,((hiff x.val).mp x.property).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hn : Nonempty {x : {x : ι // P x} // f x.val=b} := Nonempty.map e.symm hQ
  letI := hn
  unfold fibreKernel
  rw [dif_pos hn, PMF.map_comp]
  rw [← uniform_equiv_map e, PMF.map_comp]
  rfl

lemma compatible_append_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (c : Coefficient p m k) (b : Code p) (σ : Encoding p.val) :
    Compatible φ {st with entries := st.entries ++ [(c,b)]} σ ↔
      Compatible φ st σ ∧ σ (fieldIndex p (φ c))=b := by
  constructor
  · intro hs
    exact ⟨⟨fun e he => hs.1 e (List.mem_append_left _ he),hs.2⟩,
      hs.1 (c,b) (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · rintro ⟨hs,hcb⟩
    refine ⟨?_,hs.2⟩
    intro e he
    rcases List.mem_append.mp he with he|he
    · exact hs.1 e he
    · obtain rfl := List.mem_singleton.mp he
      exact hcb

theorem physical_reveal_condition {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (c : Coefficient p m k) (b : Code p)
    (hnext : Nonempty (PhysicalCompletion φ {st with entries := st.entries ++ [(c,b)]})) :
    (@fibreKernel (PhysicalCompletion φ st) (Code p) (by classical exact inferInstance) h (fun σ => σ.val (fieldIndex p (φ c))) b).map Subtype.val =
      physicalEncodingLaw φ {st with entries := st.entries ++ [(c,b)]} hnext := by
  classical
  letI : Nonempty (PhysicalCompletion φ st) := h
  unfold physicalEncodingLaw
  exact uniform_refinement (Compatible φ st) (Compatible φ {st with entries := st.entries ++ [(c,b)]})
    (fun σ => σ (fieldIndex p (φ c))) b h hnext (compatible_append_iff φ st c b)

lemma compatible_exclude_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (s : Finset (Code p)) (σ : Encoding p.val) :
    Compatible φ {st with excluded := st.excluded ∪ s} σ ↔
      Compatible φ st σ ∧ ∀ b ∈ s, b ∉ Set.range σ := by
  constructor
  · intro hs
    exact ⟨⟨hs.1,fun b hb => hs.2 b (Finset.mem_union_left _ hb)⟩,
      fun b hb => hs.2 b (Finset.mem_union_right _ hb)⟩
  · rintro ⟨hs,hn⟩
    refine ⟨hs.1,?_⟩
    intro b hb
    rcases Finset.mem_union.mp hb with hb|hb
    · exact hs.2 b hb
    · exact hn b hb

theorem physical_exclusion_condition {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (s : Finset (Code p))
    (hnext : Nonempty (PhysicalCompletion φ {st with excluded := st.excluded ∪ s})) :
    (@fibreKernel (PhysicalCompletion φ st) Bool (by classical exact inferInstance) h (fun σ => by classical exact decide (∀ b ∈ s, b ∉ Set.range σ.val)) true).map
        Subtype.val = physicalEncodingLaw φ {st with excluded := st.excluded ∪ s} hnext := by
  classical
  letI : Nonempty (PhysicalCompletion φ st) := h
  unfold physicalEncodingLaw
  apply uniform_refinement (Compatible φ st)
    (Compatible φ {st with excluded := st.excluded ∪ s})
    (fun σ => decide (∀ b ∈ s, b ∉ Set.range σ)) true h hnext
  intro σ
  simp only [decide_eq_true_eq]
  exact compatible_exclude_iff φ st s σ

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityCoupling

namespace GenericGroupWE.Main.GenericSecurityProof

lemma readCode_codeBits (p : PrimeOrder) (b : Code p) : readCode p (codeBits p b)=some b := by
  unfold readCode codeBits
  simp only [fixedBits,List.length_ofFn,ite_true]
  have hb : bitsNat (fixedBits (labelLength p.val) b.val)=b.val :=
    SamplingRuntime.word_nat_fixedBits _ _ b.isLt
  change (if h : bitsNat (fixedBits (labelLength p.val) b.val) < 2^labelLength p.val then
    some ⟨bitsNat (fixedBits (labelLength p.val) b.val),h⟩ else none)=some b
  simp only [hb,dif_pos b.isLt]

lemma codeBits_readCode (p : PrimeOrder) (x : Bits) (b : Code p)
    (h : readCode p x=some b) : codeBits p b=x := by
  unfold readCode at h
  split at h
  next hw =>
    split at h
    next hn =>
      have he : (⟨bitsNat x,hn⟩ : Code p)=b := Option.some.inj h
      subst b
      unfold codeBits
      change fixedBits (labelLength p.val) (bitsNat x)=x
      simpa only [hw] using SamplingRuntime.fixedBits_word_nat x
    next => contradiction
  next => contradiction

lemma decode_some_iff (Γ : GroupContext) (x : Bits) (a : Fin Γ.p) :
    Γ.decode x=some a ↔ label Γ.σ a=x := by
  constructor
  · intro h
    unfold GroupContext.decode at h
    exact eq_of_beq (List.find?_some (p := fun a => label Γ.σ a == x) h)
  · intro h
    rw [← h]
    exact SamplingRuntime.decode_exposed_label Γ a

lemma decode_exists_code (p : PrimeOrder) (σ : Encoding p.val) (x : Bits) :
    (∃ a, (⟨p.val,p.property,σ⟩ : GroupContext).decode x=some a) ↔
      ∃ b : Code p, readCode p x=some b ∧ b ∈ Set.range σ := by
  constructor
  · rintro ⟨a,ha⟩
    have hh := (decode_some_iff _ _ a).mp ha
    refine ⟨σ a,?_,a,rfl⟩
    rw [← hh]
    exact readCode_codeBits p (σ a)
  · rintro ⟨b,hb,a,ha⟩
    refine ⟨a,(decode_some_iff (⟨p.val,p.property,σ⟩ : GroupContext) x a).mpr ?_⟩
    change codeBits p (σ a)=x
    rw [ha]
    exact codeBits_readCode p x b hb

lemma lookupCode_some_mem {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (b : Code p) (a : Coefficient p m k)
    (h : lookupCode st b=some a) : (a,b) ∈ st.entries := by
  classical
  unfold lookupCode at h
  obtain ⟨e,he,hea⟩ := Option.map_eq_some_iff.mp h
  have heb : e.2=b := of_decide_eq_true (List.find?_some (p := fun e : Coefficient p m k × Code p => decide (e.2=b)) he)
  have hm := List.mem_of_find?_eq_some he
  simpa only [← hea,← heb,Prod.mk.eta] using hm

lemma lookupExpr_some_mem {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (a : Coefficient p m k) (b : Code p)
    (h : lookupExpr st a=some b) : (a,b) ∈ st.entries := by
  classical
  unfold lookupExpr at h
  obtain ⟨e,he,heb⟩ := Option.map_eq_some_iff.mp h
  have hea : e.1=a := of_decide_eq_true (List.find?_some (p := fun e : Coefficient p m k × Code p => decide (e.1=a)) he)
  have hm := List.mem_of_find?_eq_some he
  simpa only [← hea,← heb,Prod.mk.eta] using hm

lemma lookupCode_none_iff {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (b : Code p) :
    lookupCode st b=none ↔ b ∉ (st.entries.map Prod.snd).toFinset := by
  classical
  simp only [lookupCode,Option.map_eq_none_iff,List.find?_eq_none,decide_eq_true_eq,
    List.mem_toFinset,List.mem_map,not_exists,not_and]

lemma lookupExpr_none_iff {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (a : Coefficient p m k) :
    lookupExpr st a=none ↔ a ∉ st.entries.map Prod.fst := by
  classical
  simp only [lookupExpr,Option.map_eq_none_iff,List.find?_eq_none,decide_eq_true_eq,
    List.mem_map,not_exists,not_and]

lemma lookupCode_of_mem {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st)
    (a : Coefficient p m k) (b : Code p) (hm : (a,b) ∈ st.entries) :
    lookupCode st b=some a := by
  classical
  cases hl : lookupCode st b with
  | none =>
    exfalso
    exact ((lookupCode_none_iff st b).mp hl)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(a,b),hm,rfl⟩))
  | some c =>
    have hc := lookupCode_some_mem st b c hl
    have he := List.inj_on_of_nodup_map hw.2.1 hc hm rfl
    have hca : c=a := congrArg Prod.fst he
    simpa only [hca] using hl

lemma lookupExpr_of_mem {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st)
    (a : Coefficient p m k) (b : Code p) (hm : (a,b) ∈ st.entries) :
    lookupExpr st a=some b := by
  classical
  cases hl : lookupExpr st a with
  | none =>
    exfalso
    exact ((lookupExpr_none_iff st a).mp hl) (List.mem_map.mpr ⟨(a,b),hm,rfl⟩)
  | some c =>
    have hc := lookupExpr_some_mem st a c hl
    have he := List.inj_on_of_nodup_map hw.1 hc hm rfl
    have hcb : c=b := congrArg Prod.snd he
    simpa only [hcb] using hl

lemma excludeOperand_entries {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : (excludeOperand st x).entries=st.entries := by
  classical
  unfold excludeOperand
  split
  · rfl
  · split <;> rfl

lemma lookupCode_excludeOperand {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) (b : Code p) :
    lookupCode (excludeOperand st x) b=lookupCode st b := by
  classical
  unfold lookupCode
  rw [excludeOperand_entries]

lemma excludeOperand_known {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) (a : Coefficient p m k)
    (h : lookupOperand st x=some a) : excludeOperand st x=st := by
  classical
  unfold lookupOperand at h
  cases hr : readCode p x with
  | none => simp only [hr,Option.bind_none,reduceCtorEq] at h
  | some b =>
    have hb : lookupCode st b=some a := by simpa only [hr,Option.bind_some] using h
    simp only [excludeOperand,hr,hb,Option.isNone_some,Bool.false_eq_true,ite_false]


lemma known_operand_encode {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ : Encoding p.val) (hσ : Compatible φ st σ) (x : Bits) (a : Coefficient p m k)
    (ha : lookupOperand st x=some a) : encodeField σ (φ a)=x := by
  classical
  unfold lookupOperand at ha
  cases hx : readCode p x with
  | none => simp only [hx,Option.bind_none,reduceCtorEq] at ha
  | some b =>
    have hb : lookupCode st b=some a := by simpa only [hx,Option.bind_some] using ha
    have hφ := hσ.1 (a,b) (lookupCode_some_mem st b a hb)
    change codeBits p (σ (fieldIndex p (φ a)))=x
    rw [hφ]
    exact codeBits_readCode p x b hx

lemma physical_query_known {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ : Encoding p.val) (hσ : Compatible φ st σ) (subtract : Bool) (x y : Bits)
    (a b : Coefficient p m k) (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) :
    (⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y =
      some (codeBits p (σ (fieldIndex p (φ (if subtract then a-b else a+b))))) := by
  rw [← known_operand_encode φ st σ hσ x a ha,← known_operand_encode φ st σ hσ y b hb]
  have hh := SamplingRuntime.query_encodeField p σ subtract (φ a) (φ b)
  cases subtract <;> simpa only [SamplingRuntime.encodingContext,Bool.false_eq_true,ite_false,
    ite_true,map_sub,map_add,encodeField,label,codeBits,fieldIndex] using hh

lemma physical_decode_unknown {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (σ : Encoding p.val) (x : Bits)
    (hx : lookupOperand st x=none)
    (hguess : ∀ b : Code p, readCode p x=some b → lookupCode st b=none → b ∉ Set.range σ) :
    (⟨p.val,p.property,σ⟩ : GroupContext).decode x=none := by
  classical
  cases hd : (⟨p.val,p.property,σ⟩ : GroupContext).decode x with
  | none => rfl
  | some a =>
    exfalso
    have hl := (decode_some_iff (⟨p.val,p.property,σ⟩ : GroupContext) x a).mp hd
    have hp : readCode p x=some (σ a) := by
      rw [← hl]
      exact readCode_codeBits p (σ a)
    have hn : lookupCode st (σ a)=none := by
      simpa only [lookupOperand,hp,Option.bind_some] using hx
    exact hguess (σ a) hp hn ⟨a,rfl⟩

lemma physical_query_invalid {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (σ : Encoding p.val) (subtract : Bool) (x y : Bits)
    (hguess : ¬ stepGuess st σ x y)
    (hinvalid : lookupOperand st x=none ∨ lookupOperand st y=none) :
    (⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y=none := by
  rcases hinvalid with hx|hy
  · have hd := physical_decode_unknown st σ x hx (fun b hb hn hi => hguess ⟨b,Or.inl hb,hn,hi⟩)
    simp only [GroupContext.query,hd,Option.bind_eq_bind,Option.bind_none]
  · have hd := physical_decode_unknown st σ y hy (fun b hb hn hi => hguess ⟨b,Or.inr hb,hn,hi⟩)
    cases hdx : (⟨p.val,p.property,σ⟩ : GroupContext).decode x <;>
      simp only [GroupContext.query,hd,hdx,Option.bind_eq_bind,Option.bind_none,Option.bind_some]


def traceCollision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) : Prop :=
  ∃ e ∈ st.entries, ∃ f ∈ st.entries, e.1 ≠ f.1 ∧ φ e.1=φ f.1

def traceGuess {p : PrimeOrder} {m k : ℕ} (σ : Encoding p.val) (st : SimulatorState p m k) : Prop :=
  ∃ b ∈ st.excluded, b ∈ Set.range σ

noncomputable def physicalAllocate {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (c : Coefficient p m k) : SimulatorState p m k :=
  match lookupExpr st c with
  | some _ => st
  | none => {st with entries := st.entries ++ [(c,σ (fieldIndex p (φ c)))]}

/-- Explicit proof-side coupled traversal. Before the first discrepancy it uses
physical replies and physically revealed labels. At a bad guess or collision it
continues the ordinary simulator, leaving the already sampled real encoding fixed.
This is total data, not a faithfulness assumption. -/
noncomputable def coupledTree {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (q : ℕ) (tree : QueryTree q) (st : SimulatorState p m k) : PMF (Bool × SimulatorState p m k) := by
  classical
  exact if st.dead then pure (false,st) else
    match tree with
    | .halt bit => pure (bit,st)
    | .query subtract x y continuation =>
      if stepGuess st σ x y ∨ stepCollision φ st subtract x y then simulatorTree _ tree st else
      let next := excludeOperand (excludeOperand st x) y
      let next := match lookupOperand st x,lookupOperand st y with
        | some a,some b => physicalAllocate φ σ next (if subtract then a-b else a+b)
        | _,_ => next
      coupledTree φ σ _
        (continuation ((⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y)) next
termination_by q

noncomputable def coupledTreeLaw {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (q : ℕ) (tree : QueryTree q) :
    PMF (Encoding p.val × (Bool × SimulatorState p m k)) :=
  (physicalEncodingLaw φ st h).bind fun σ => (coupledTree φ σ q tree st).map fun z => (σ,z)

lemma coupledTreeLaw_encoding {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (q : ℕ) (tree : QueryTree q) :
    (coupledTreeLaw φ st h q tree).map Prod.fst=physicalEncodingLaw φ st h := by
  unfold coupledTreeLaw
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  have hc (σ : Encoding p.val) : (coupledTree φ σ q tree st).map (fun _ => σ)=pure σ := PMF.map_const (coupledTree φ σ q tree st) σ
  simp only [hc]
  exact PMF.bind_pure _

lemma coupledTreeLaw_output {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (q : ℕ) (tree : QueryTree q) :
    (coupledTreeLaw φ st h q tree).map Prod.snd =
      (physicalEncodingLaw φ st h).bind (fun σ => coupledTree φ σ q tree st) := by
  unfold coupledTreeLaw
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext σ
  exact PMF.map_id _


lemma physicalAllocate_map {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (c : Coefficient p m k)
    (hnew : ∀ e ∈ st.entries, φ c ≠ φ e.1) (hfresh : (freshCodes st).Nonempty)
    (hlive : st.dead=false) :
    (physicalEncodingLaw φ st h).map (fun σ => physicalAllocate φ σ st c) =
      (allocate st c).map Prod.snd := by
  classical
  have hc : lookupExpr st c=none := by
    cases hl : lookupExpr st c with
    | none => rfl
    | some b => exact False.elim (hnew (c,b) (lookupExpr_some_mem st c b hl) rfl)
  simp only [physicalAllocate,hc,allocate,hlive,Bool.false_eq_true,ite_false,
    dif_pos hfresh,PMF.map_comp,Function.comp_def]
  have hh := congrArg (fun law : PMF (Code p) => law.map fun b =>
    {st with entries := st.entries ++ [(c,b)]}) (fresh_physical_forward φ st h c hnew hfresh)
  simpa only [PMF.map_comp,Function.comp_def,hlive] using hh

lemma freshCodes_nonempty_physical {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (c : Coefficient p m k)
    (hnew : ∀ e ∈ st.entries, φ c ≠ φ e.1) : (freshCodes st).Nonempty := by
  classical
  obtain ⟨σ,hσ⟩ := h
  refine ⟨σ (fieldIndex p (φ c)),?_⟩
  simp only [freshCodes,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb
    obtain ⟨e,he,heb⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    have hi := σ.injective ((hσ.1 e he).trans heb)
    exact hnew e he ((fieldIndex_injective p hi).symm)
  · intro hb
    exact hσ.2 _ hb ⟨fieldIndex p (φ c),rfl⟩

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityTrace

namespace GenericGroupWE.Main.GenericSecurityProof

lemma bind_congr_support_local {ι α : Type*} (law : PMF ι) (f g : ι → PMF α)
    (h : ∀ x ∈ law.support, f x=g x) : law.bind f=law.bind g := by
  apply PMF.ext
  intro a
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : law x=0
  · simp only [hx,zero_mul]
  · rw [h x hx]

lemma uniform_fibre_bind {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) (g : ι → PMF α) :
    (PMF.uniformOfFintype ι).bind g =
      ((PMF.uniformOfFintype ι).map f).bind (fun b => (fibreKernel f b).bind g) := by
  rw [← PMF.bind_bind,uniform_fibre_recombine]

lemma uniform_bind_of_fibres {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) (g : ι → PMF α) (ν : PMF α)
    (h : ∀ b (hb : Nonempty {x : ι // f x=b}),
      (@PMF.uniformOfFintype {x : ι // f x=b} (by classical exact inferInstance) hb).bind
        (fun x => g x.val) = ν) : (PMF.uniformOfFintype ι).bind g=ν := by
  classical
  rw [uniform_fibre_bind f g]
  calc
    _ = ((PMF.uniformOfFintype ι).map f).bind (fun _ => ν) := by
      apply bind_congr_support_local
      intro b hb
      obtain ⟨x,hx,hxb⟩ := (PMF.mem_support_map_iff f (PMF.uniformOfFintype ι) b).mp hb
      have hn : Nonempty {x : ι // f x=b} := ⟨⟨x,hxb⟩⟩
      unfold fibreKernel
      rw [dif_pos hn,PMF.bind_map]
      apply PMF.ext
      intro a
      have hh := congrArg (fun law : PMF α => law a) (h b hn)
      simpa only [PMF.bind_apply,PMF.uniformOfFintype_apply,← Nat.card_eq_fintype_card,
        Function.comp_def] using hh
    _ = ν := PMF.bind_const _ _


noncomputable def operandUnknownCodes {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : Finset (Code p) := by
  classical
  exact match readCode p x with
  | none => ∅
  | some b => if (lookupCode st b).isNone then {b} else ∅

lemma mem_operandUnknownCodes {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) (b : Code p) :
    b ∈ operandUnknownCodes st x ↔ readCode p x=some b ∧ lookupCode st b=none := by
  classical
  cases hx : readCode p x with
  | none => simp [operandUnknownCodes,hx]
  | some c =>
    by_cases hbc : b=c
    · subst b
      cases hc : lookupCode st c <;> simp [operandUnknownCodes,hx,hc]
    · cases hc : lookupCode st c <;> simp [operandUnknownCodes,hx,hc,hbc,Ne.symm hbc]

lemma excludeOperand_dead {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : (excludeOperand st x).dead=st.dead := by
  classical
  unfold excludeOperand
  split
  · rfl
  · split <;> rfl

lemma excludeOperand_excluded {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) :
    (excludeOperand st x).excluded=st.excluded ∪ operandUnknownCodes st x := by
  classical
  cases hx : readCode p x with
  | none => simp [excludeOperand,operandUnknownCodes,hx]
  | some c => cases hc : lookupCode st c <;>
      simp [excludeOperand,operandUnknownCodes,hx,hc,Finset.union_singleton]

lemma operandUnknownCodes_exclude {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x y : Bits) :
    operandUnknownCodes (excludeOperand st x) y=operandUnknownCodes st y := by
  classical
  unfold operandUnknownCodes
  cases hy : readCode p y <;> simp only [lookupCode_excludeOperand]

noncomputable def unknownOperandCodes {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x y : Bits) : Finset (Code p) :=
  operandUnknownCodes st x ∪ operandUnknownCodes st y

lemma stepGuess_unknownCodes {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (σ : Encoding p.val) (x y : Bits) :
    stepGuess st σ x y ↔ ∃ b ∈ unknownOperandCodes st x y, b ∈ Set.range σ := by
  constructor
  · rintro ⟨b,hb,hn,hi⟩
    refine ⟨b,?_,hi⟩
    rcases hb with hx|hy
    · exact Finset.mem_union_left _ ((mem_operandUnknownCodes st x b).mpr ⟨hx,hn⟩)
    · exact Finset.mem_union_right _ ((mem_operandUnknownCodes st y b).mpr ⟨hy,hn⟩)
  · rintro ⟨b,hb,hi⟩
    rcases Finset.mem_union.mp hb with hb|hb
    · obtain ⟨hx,hn⟩ := (mem_operandUnknownCodes st x b).mp hb
      exact ⟨b,Or.inl hx,hn,hi⟩
    · obtain ⟨hy,hn⟩ := (mem_operandUnknownCodes st y b).mp hb
      exact ⟨b,Or.inr hy,hn,hi⟩

lemma excludeOperands_eq {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x y : Bits) :
    excludeOperand (excludeOperand st x) y=
      {st with excluded := st.excluded ∪ unknownOperandCodes st x y} := by
  have he : (excludeOperand (excludeOperand st x) y).entries=st.entries := by
    rw [excludeOperand_entries,excludeOperand_entries]
  have hd : (excludeOperand (excludeOperand st x) y).dead=st.dead := by
    rw [excludeOperand_dead,excludeOperand_dead]
  have hf : (excludeOperand (excludeOperand st x) y).excluded=
      st.excluded ∪ unknownOperandCodes st x y := by
    rw [excludeOperand_excluded,excludeOperand_excluded,operandUnknownCodes_exclude]
    exact Finset.union_assoc _ _ _
  cases hnext : excludeOperand (excludeOperand st x) y
  simp only [hnext] at he hd hf
  cases st
  simp_all

lemma WellFormed_exclude {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st) (x : Bits) :
    WellFormed (excludeOperand st x) := by
  classical
  refine ⟨?_,?_,?_⟩
  · rw [excludeOperand_entries]
    exact hw.1
  · rw [excludeOperand_entries]
    exact hw.2.1
  · rw [excludeOperand_entries,excludeOperand_excluded]
    apply Finset.disjoint_left.mpr
    intro b hb hf
    rcases Finset.mem_union.mp hf with hf|hf
    · exact (Finset.disjoint_left.mp hw.2.2) hb hf
    · obtain ⟨hx,hn⟩ := (mem_operandUnknownCodes st x b).mp hf
      exact ((lookupCode_none_iff st b).mp hn) hb


lemma stepCollision_invalid {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (subtract : Bool) (x y : Bits)
    (hi : lookupOperand st x=none ∨ lookupOperand st y=none) :
    ¬ stepCollision φ st subtract x y := by
  rintro ⟨a,b,ha,hb,rest⟩
  rcases hi with hx|hy
  · rw [hx] at ha
    contradiction
  · rw [hy] at hb
    contradiction

lemma simulatorStep_invalid {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits) (hl : st.dead=false)
    (hi : lookupOperand st x=none ∨ lookupOperand st y=none) :
    simulatorStep st subtract x y=PMF.pure (none,excludeOperand (excludeOperand st x) y) := by
  classical
  unfold simulatorStep
  simp only [hl,Bool.false_eq_true,ite_false]
  rcases hi with hx|hy
  · rw [hx]
    cases lookupOperand st y <;> rfl
  · rw [hy]
    cases lookupOperand st x <;> rfl

lemma simulatorTree_invalid {p : PrimeOrder} {m k q : ℕ}
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (hi : lookupOperand st x=none ∨ lookupOperand st y=none) :
    simulatorTree (q+1) (.query subtract x y continuation) st=
      simulatorTree q (continuation none) (excludeOperand (excludeOperand st x) y) := by
  classical
  rw [simulatorTree]
  simp only [hl,Bool.false_eq_true,ite_false]
  rw [simulatorStep_invalid st subtract x y hl hi]
  exact PMF.pure_bind _ _

lemma coupledTree_invalid_good {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (σ : Encoding p.val) (subtract : Bool) (x y : Bits)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (hi : lookupOperand st x=none ∨ lookupOperand st y=none) (hg : ¬ stepGuess st σ x y) :
    coupledTree φ σ (q+1) (.query subtract x y continuation) st=
      coupledTree φ σ q (continuation none) (excludeOperand (excludeOperand st x) y) := by
  classical
  rw [coupledTree]
  simp only [hl,Bool.false_eq_true,ite_false,hg,stepCollision_invalid φ st subtract x y hi,
    false_or,ite_false]
  rw [physical_query_invalid st σ subtract x y hg hi]
  rcases hi with hx|hy
  · rw [hx]
  · rw [hy]
    cases lookupOperand st x <;> rfl

lemma compatible_excludeOperands {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (σ : Encoding p.val) (x y : Bits) :
    Compatible φ (excludeOperand (excludeOperand st x) y) σ ↔
      Compatible φ st σ ∧ ¬ stepGuess st σ x y := by
  rw [excludeOperands_eq,compatible_exclude_iff,stepGuess_unknownCodes]
  simp only [not_exists,not_and]


lemma coupledTree_invalid_branch {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (continuation : Option Bits → QueryTree q)
    (hl : st.dead=false) (hi : lookupOperand st x=none ∨ lookupOperand st y=none)
    (ih : ∀ hnext : Nonempty (PhysicalCompletion φ (excludeOperand (excludeOperand st x) y)),
      (physicalEncodingLaw φ (excludeOperand (excludeOperand st x) y) hnext).bind
        (fun σ => coupledTree φ σ q (continuation none) (excludeOperand (excludeOperand st x) y)) =
      simulatorTree q (continuation none) (excludeOperand (excludeOperand st x) y)) :
    (physicalEncodingLaw φ st h).bind
      (fun σ => coupledTree φ σ (q+1) (.query subtract x y continuation) st) =
    simulatorTree (q+1) (.query subtract x y continuation) st := by
  classical
  let next := excludeOperand (excludeOperand st x) y
  letI : Nonempty (PhysicalCompletion φ st) := h
  rw [simulatorTree_invalid st subtract x y continuation hl hi]
  unfold physicalEncodingLaw
  rw [PMF.bind_map]
  apply uniform_bind_of_fibres (fun σ : PhysicalCompletion φ st => decide (¬ stepGuess st σ.val x y))
  intro b hb
  cases b with
  | false =>
    have he (σ : {σ : PhysicalCompletion φ st // decide (¬ stepGuess st σ.val x y)=false}) :
        coupledTree φ σ.val.val (q+1) (.query subtract x y continuation) st =
          simulatorTree q (continuation none) next := by
      have hg : stepGuess st σ.val.val x y := by simpa only [decide_eq_false_iff_not,not_not] using σ.property
      rw [coupledTree]
      simp only [hl,Bool.false_eq_true,ite_false,hg,true_or,ite_true]
      exact simulatorTree_invalid st subtract x y continuation hl hi
    simp only [Function.comp_def]
    simp_rw [he]
    exact PMF.bind_const _ _
  | true =>
    let σ₀ := Classical.choice hb
    have hg₀ : ¬ stepGuess st σ₀.val.val x y := of_decide_eq_true σ₀.property
    have hnext : Nonempty (PhysicalCompletion φ next) :=
      ⟨⟨σ₀.val.val,(compatible_excludeOperands φ st σ₀.val.val x y).mpr ⟨σ₀.val.property,hg₀⟩⟩⟩
    have he (σ : {σ : PhysicalCompletion φ st // decide (¬ stepGuess st σ.val x y)=true}) :
        coupledTree φ σ.val.val (q+1) (.query subtract x y continuation) st =
          coupledTree φ σ.val.val q (continuation none) next := by
      exact coupledTree_invalid_good φ st σ.val.val subtract x y continuation hl hi
        (of_decide_eq_true σ.property)
    simp only [Function.comp_def]
    simp_rw [he]
    have hkernel :
        (@fibreKernel (PhysicalCompletion φ st) Bool inferInstance h
          (fun σ => decide (¬ stepGuess st σ.val x y)) true).map Subtype.val =
          physicalEncodingLaw φ next hnext := by
      apply uniform_refinement (Compatible φ st) (Compatible φ next)
        (fun σ => decide (¬ stepGuess st σ x y)) true h hnext
      intro σ
      simpa only [decide_eq_true_eq] using compatible_excludeOperands φ st σ x y
    unfold fibreKernel at hkernel
    rw [dif_pos hb,PMF.map_comp] at hkernel
    have hh := congrArg (fun law : PMF (Encoding p.val) =>
      law.bind fun σ => coupledTree φ σ q (continuation none) next) hkernel
    rw [PMF.bind_map] at hh
    calc
      _ = (physicalEncodingLaw φ next hnext).bind
          (fun σ => coupledTree φ σ q (continuation none) next) := by
        apply PMF.ext
        intro out
        have hp := congrArg (fun law : PMF (Bool × SimulatorState p m k) => law out) hh
        simpa only [PMF.bind_apply,PMF.uniformOfFintype_apply,← Nat.card_eq_fintype_card,
          Function.comp_def] using hp
      _ = _ := ih hnext


lemma stepGuess_known {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (σ : Encoding p.val) (x y : Bits)
    (a b : Coefficient p m k) (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) :
    ¬ stepGuess st σ x y := by
  rintro ⟨code,hread,hn,hi⟩
  rcases hread with hx|hy
  · have he : lookupOperand st x=none := by simp only [lookupOperand,hx,hn,Option.bind_some]
    rw [he] at ha
    contradiction
  · have he : lookupOperand st y=none := by simp only [lookupOperand,hy,hn,Option.bind_some]
    rw [he] at hb
    contradiction

lemma simulatorTree_known_existing {p : PrimeOrder} {m k q : ℕ}
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) (code : Code p)
    (hc : lookupExpr st (if subtract then a-b else a+b)=some code) :
    simulatorTree (q+1) (.query subtract x y continuation) st =
      simulatorTree q (continuation (some (codeBits p code))) st := by
  classical
  rw [simulatorTree]
  simp only [hl,Bool.false_eq_true,ite_false]
  have he : excludeOperand (excludeOperand st x) y=st := by
    rw [excludeOperand_known st x a ha,excludeOperand_known st y b hb]
  simp only [simulatorStep,hl,Bool.false_eq_true,ite_false,he,ha,hb,allocate,hc]
  change ((PMF.pure (some code,st)).map (fun result => (result.1.map (codeBits p),result.2))).bind
    (fun result => simulatorTree q (continuation result.1) result.2)=_
  rw [PMF.pure_map,PMF.pure_bind]
  rfl

lemma coupledTree_known_existing {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (σ : Encoding p.val) (hσ : Compatible φ st σ)
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) (code : Code p)
    (hc : lookupExpr st (if subtract then a-b else a+b)=some code)
    (hcollision : ¬ stepCollision φ st subtract x y) :
    coupledTree φ σ (q+1) (.query subtract x y continuation) st=
      coupledTree φ σ q (continuation (some (codeBits p code))) st := by
  classical
  have hguess := stepGuess_known st σ x y a b ha hb
  have he : excludeOperand (excludeOperand st x) y=st := by
    rw [excludeOperand_known st x a ha,excludeOperand_known st y b hb]
  rw [coupledTree]
  simp only [hl,Bool.false_eq_true,ite_false,hguess,hcollision,false_or,he,ha,hb,physicalAllocate,hc]
  rw [physical_query_known φ st σ hσ subtract x y a b ha hb]
  have hφ := hσ.1 ((if subtract then a-b else a+b),code) (lookupExpr_some_mem st _ code hc)
  rw [hφ]

lemma coupledTree_existing_branch {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) (code : Code p)
    (hc : lookupExpr st (if subtract then a-b else a+b)=some code)
    (hcollision : ¬ stepCollision φ st subtract x y)
    (ih : (physicalEncodingLaw φ st h).bind
      (fun σ => coupledTree φ σ q (continuation (some (codeBits p code))) st)=
      simulatorTree q (continuation (some (codeBits p code))) st) :
    (physicalEncodingLaw φ st h).bind
      (fun σ => coupledTree φ σ (q+1) (.query subtract x y continuation) st)=
      simulatorTree (q+1) (.query subtract x y continuation) st := by
  rw [simulatorTree_known_existing st subtract x y a b continuation hl ha hb code hc]
  rw [← ih]
  unfold physicalEncodingLaw
  rw [PMF.bind_map,PMF.bind_map]
  congr 1
  funext σ
  exact coupledTree_known_existing φ st σ.val σ.property subtract x y a b continuation hl ha hb code hc hcollision


lemma uniform_bind_compare_fibres {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) (g : ι → PMF α) (ν : κ → PMF α)
    (h : ∀ b (hb : Nonempty {x : ι // f x=b}),
      (@PMF.uniformOfFintype {x : ι // f x=b} (by classical exact inferInstance) hb).bind
        (fun x => g x.val) = ν b) :
    (PMF.uniformOfFintype ι).bind g=((PMF.uniformOfFintype ι).map f).bind ν := by
  classical
  rw [uniform_fibre_bind f g]
  apply bind_congr_support_local
  intro b hb
  obtain ⟨x,hx,hxb⟩ := (PMF.mem_support_map_iff f (PMF.uniformOfFintype ι) b).mp hb
  have hn : Nonempty {x : ι // f x=b} := ⟨⟨x,hxb⟩⟩
  unfold fibreKernel
  rw [dif_pos hn,PMF.bind_map]
  apply PMF.ext
  intro a
  have hh := congrArg (fun law : PMF α => law a) (h b hn)
  simpa only [PMF.bind_apply,PMF.uniformOfFintype_apply,← Nat.card_eq_fintype_card,
    Function.comp_def] using hh

lemma physical_new_code_fresh {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (σ : Encoding p.val) (hσ : Compatible φ st σ) (c : Coefficient p m k)
    (hnew : ∀ e ∈ st.entries, φ c ≠ φ e.1) : σ (fieldIndex p (φ c)) ∈ freshCodes st := by
  classical
  simp only [freshCodes,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hb
    obtain ⟨e,he,heb⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    have hi := σ.injective ((hσ.1 e he).trans heb)
    exact hnew e he ((fieldIndex_injective p hi).symm)
  · intro hb
    exact hσ.2 _ hb ⟨fieldIndex p (φ c),rfl⟩

lemma WellFormed_append {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st) (c : Coefficient p m k) (code : Code p)
    (hc : lookupExpr st c=none) (hb : code ∈ freshCodes st) :
    WellFormed {st with entries := st.entries ++ [(c,code)]} := by
  classical
  have hcm : c ∉ st.entries.map Prod.fst := (lookupExpr_none_iff st c).mp hc
  have hbm : code ∉ (st.entries.map Prod.snd).toFinset ∧ code ∉ st.excluded := by
    simpa only [freshCodes,Finset.mem_filter,Finset.mem_univ,true_and] using hb
  refine ⟨?_,?_,?_⟩
  · change ((st.entries ++ [(c,code)]).map Prod.fst).Nodup
    simpa only [List.map_append,List.map_singleton,List.concat_eq_append] using
      List.Nodup.concat hcm hw.1
  · change ((st.entries ++ [(c,code)]).map Prod.snd).Nodup
    simpa only [List.map_append,List.map_singleton,List.concat_eq_append] using
      List.Nodup.concat (show code ∉ st.entries.map Prod.snd from fun h => hbm.1 (List.mem_toFinset.mpr h)) hw.2.1
  · apply Finset.disjoint_left.mpr
    intro b hb he
    have hm := List.mem_toFinset.mp hb
    simp only [List.map_append,List.map_singleton,List.mem_append,List.mem_singleton] at hm
    rcases hm with hm|rfl
    · exact (Finset.disjoint_left.mp hw.2.2) (List.mem_toFinset.mpr hm) he
    · exact hbm.2 he

lemma fresh_value_of_no_collision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b)
    (hc : lookupExpr st (if subtract then a-b else a+b)=none)
    (hcollision : ¬ stepCollision φ st subtract x y) :
    ∀ e ∈ st.entries, φ (if subtract then a-b else a+b) ≠ φ e.1 := by
  intro e he hφ
  have hn : (if subtract then a-b else a+b) ≠ e.1 := by
    intro h
    exact ((lookupExpr_none_iff st _).mp hc) (h.symm ▸ List.mem_map.mpr ⟨e,he,rfl⟩)
  exact hcollision ⟨a,b,ha,hb,e,he,hn,hφ⟩


lemma simulatorTree_known_fresh {p : PrimeOrder} {m k q : ℕ}
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b)
    (hc : lookupExpr st (if subtract then a-b else a+b)=none) (hfresh : (freshCodes st).Nonempty) :
    simulatorTree (q+1) (.query subtract x y continuation) st =
      (PMF.uniformOfFinset (freshCodes st) hfresh).bind (fun code =>
        simulatorTree q (continuation (some (codeBits p code)))
          {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]}) := by
  classical
  rw [simulatorTree]
  simp only [hl,Bool.false_eq_true,ite_false]
  have he : excludeOperand (excludeOperand st x) y=st := by
    rw [excludeOperand_known st x a ha,excludeOperand_known st y b hb]
  simp only [simulatorStep,hl,Bool.false_eq_true,ite_false,he,ha,hb,allocate,hc,dif_pos hfresh]
  rw [PMF.bind_map,PMF.bind_map]
  rfl

lemma coupledTree_known_fresh {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (σ : Encoding p.val) (hσ : Compatible φ st σ)
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b)
    (hc : lookupExpr st (if subtract then a-b else a+b)=none)
    (hcollision : ¬ stepCollision φ st subtract x y) :
    coupledTree φ σ (q+1) (.query subtract x y continuation) st=
      coupledTree φ σ q
        (continuation (some (codeBits p (σ (fieldIndex p (φ (if subtract then a-b else a+b)))))))
        {st with entries := st.entries ++ [((if subtract then a-b else a+b),σ (fieldIndex p (φ (if subtract then a-b else a+b))))]} := by
  classical
  have hguess := stepGuess_known st σ x y a b ha hb
  have he : excludeOperand (excludeOperand st x) y=st := by
    rw [excludeOperand_known st x a ha,excludeOperand_known st y b hb]
  rw [coupledTree]
  simp only [hl,Bool.false_eq_true,ite_false,hguess,hcollision,false_or,he,ha,hb,physicalAllocate,hc]
  rw [physical_query_known φ st σ hσ subtract x y a b ha hb]

lemma coupledTree_fresh_branch {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b)
    (hc : lookupExpr st (if subtract then a-b else a+b)=none)
    (hcollision : ¬ stepCollision φ st subtract x y)
    (ih : ∀ (code : Code p), code ∈ freshCodes st →
      ∀ hnext : Nonempty (PhysicalCompletion φ
        {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]}),
      (physicalEncodingLaw φ {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]} hnext).bind
        (fun σ => coupledTree φ σ q (continuation (some (codeBits p code)))
          {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]})=
      simulatorTree q (continuation (some (codeBits p code)))
        {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]}) :
    (physicalEncodingLaw φ st h).bind
      (fun σ => coupledTree φ σ (q+1) (.query subtract x y continuation) st)=
      simulatorTree (q+1) (.query subtract x y continuation) st := by
  classical
  let c := if subtract then a-b else a+b
  have hnew := fresh_value_of_no_collision φ st subtract x y a b ha hb hc hcollision
  have hfresh := freshCodes_nonempty_physical φ st h c hnew
  letI : Nonempty (PhysicalCompletion φ st) := h
  rw [simulatorTree_known_fresh st subtract x y a b continuation hl ha hb hc hfresh]
  rw [← fresh_physical_forward φ st h c hnew hfresh]
  unfold physicalEncodingLaw
  rw [PMF.bind_map,PMF.map_comp]
  apply uniform_bind_compare_fibres (fun σ : PhysicalCompletion φ st => σ.val (fieldIndex p (φ c)))
  intro code hcode
  let σ₀ := Classical.choice hcode
  have hbfresh : code ∈ freshCodes st := by
    rw [← σ₀.property]
    exact physical_new_code_fresh φ st σ₀.val.val σ₀.val.property c hnew
  have hnext : Nonempty (PhysicalCompletion φ {st with entries := st.entries ++ [(c,code)]}) :=
    ⟨⟨σ₀.val.val,(compatible_append_iff φ st c code σ₀.val.val).mpr ⟨σ₀.val.property,σ₀.property⟩⟩⟩
  have he (σ : {σ : PhysicalCompletion φ st // σ.val (fieldIndex p (φ c))=code}) :
      coupledTree φ σ.val.val (q+1) (.query subtract x y continuation) st=
        coupledTree φ σ.val.val q (continuation (some (codeBits p code)))
          {st with entries := st.entries ++ [(c,code)]} := by
    rw [coupledTree_known_fresh φ st σ.val.val σ.val.property subtract x y a b continuation hl ha hb hc hcollision]
    rw [σ.property]
  simp only [Function.comp_def]
  simp_rw [he]
  have hkernel := physical_reveal_condition φ st h c code hnext
  unfold fibreKernel at hkernel
  rw [dif_pos hcode,PMF.map_comp] at hkernel
  have hh := congrArg (fun law : PMF (Encoding p.val) => law.bind fun σ =>
    coupledTree φ σ q (continuation (some (codeBits p code)))
      {st with entries := st.entries ++ [(c,code)]}) hkernel
  rw [PMF.bind_map] at hh
  calc
    _ = (physicalEncodingLaw φ {st with entries := st.entries ++ [(c,code)]} hnext).bind
        (fun σ => coupledTree φ σ q (continuation (some (codeBits p code)))
          {st with entries := st.entries ++ [(c,code)]}) := by
      apply PMF.ext
      intro out
      have hp := congrArg (fun law : PMF (Bool × SimulatorState p m k) => law out) hh
      simpa only [PMF.bind_apply,PMF.uniformOfFintype_apply,← Nat.card_eq_fintype_card,
        Function.comp_def] using hp
    _ = _ := ih code hbfresh hnext


/-- Exact simulator marginal of the explicit physical traversal. This theorem
says nothing by itself about output agreement or the probability of bad events. -/
theorem coupledTree_right_marginal {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (q : ℕ) (tree : QueryTree q)
    (st : SimulatorState p m k) (hw : WellFormed st)
    (h : Nonempty (PhysicalCompletion φ st)) :
    (coupledTreeLaw φ st h q tree).map Prod.snd=simulatorTree q tree st := by
  classical
  rw [coupledTreeLaw_output]
  induction tree generalizing st with
  | halt bit =>
    by_cases hd : st.dead=true
    · simp only [coupledTree,simulatorTree,hd,ite_true]
      exact PMF.bind_const _ _
    · have hl : st.dead=false := Bool.eq_false_iff.mpr hd
      simp only [coupledTree,simulatorTree,hl,Bool.false_eq_true,ite_false]
      exact PMF.bind_const _ _
  | @query q subtract x y continuation ih =>
    by_cases hd : st.dead=true
    · simp only [coupledTree,simulatorTree,hd,ite_true]
      exact PMF.bind_const _ _
    · have hl : st.dead=false := Bool.eq_false_iff.mpr hd
      by_cases hcollision : stepCollision φ st subtract x y
      · have he (σ : Encoding p.val) :
            coupledTree φ σ (q+1) (.query subtract x y continuation) st =
            simulatorTree (q+1) (.query subtract x y continuation) st := by
          simp only [coupledTree,hl,Bool.false_eq_true,ite_false,hcollision,or_true,ite_true]
        simp_rw [he]
        exact PMF.bind_const _ _
      · by_cases hi : lookupOperand st x=none ∨ lookupOperand st y=none
        · apply coupledTree_invalid_branch φ st hw h subtract x y continuation hl hi
          intro hnext
          exact ih none _ (WellFormed_exclude _ (WellFormed_exclude st hw x) y) hnext
        · cases hx : lookupOperand st x with
          | none => exact False.elim (hi (Or.inl hx))
          | some a =>
            cases hy : lookupOperand st y with
            | none => exact False.elim (hi (Or.inr hy))
            | some b =>
              cases hc : lookupExpr st (if subtract then a-b else a+b) with
              | none =>
                apply coupledTree_fresh_branch φ st h subtract x y a b continuation hl hx hy hc hcollision
                intro code hbfresh hnext
                exact ih (some (codeBits p code)) _ (WellFormed_append st hw _ code hc hbfresh) hnext
              | some code =>
                apply coupledTree_existing_branch φ st h subtract x y a b continuation hl hx hy code hc hcollision
                exact ih (some (codeBits p code)) st hw h

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecuritySafety

namespace GenericGroupWE.Main.GenericSecurityProof

def StateExtends {p : PrimeOrder} {m k : ℕ} (st next : SimulatorState p m k) : Prop :=
  st.entries <+: next.entries ∧ st.excluded ⊆ next.excluded

lemma StateExtends_refl {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k) : StateExtends st st :=
  ⟨List.prefix_refl _,Finset.Subset.refl _⟩

lemma StateExtends_trans {p : PrimeOrder} {m k : ℕ} {a b c : SimulatorState p m k}
    (hab : StateExtends a b) (hbc : StateExtends b c) : StateExtends a c :=
  ⟨hab.1.trans hbc.1,hab.2.trans hbc.2⟩

lemma StateExtends_collision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) {st next : SimulatorState p m k}
    (he : StateExtends st next) (hc : traceCollision φ st) : traceCollision φ next := by
  obtain ⟨a,ha,b,hb,hne,heq⟩ := hc
  exact ⟨a,he.1.subset ha,b,he.1.subset hb,hne,heq⟩

lemma StateExtends_guess {p : PrimeOrder} {m k : ℕ} (σ : Encoding p.val)
    {st next : SimulatorState p m k} (he : StateExtends st next) (hg : traceGuess σ st) :
    traceGuess σ next := by
  obtain ⟨b,hb,hi⟩ := hg
  exact ⟨b,he.2 hb,hi⟩

lemma excludeOperand_extends {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) : StateExtends st (excludeOperand st x) := by
  refine ⟨?_,?_⟩
  · rw [excludeOperand_entries]
  · rw [excludeOperand_excluded]
    exact Finset.subset_union_left

lemma physicalAllocate_extends {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (c : Coefficient p m k) : StateExtends st (physicalAllocate φ σ st c) := by
  unfold physicalAllocate
  cases lookupExpr st c with
  | none => exact ⟨⟨[(c,σ (fieldIndex p (φ c)))],rfl⟩,Finset.Subset.refl _⟩
  | some b => exact StateExtends_refl st

lemma pure_support_eq_local {α : Type*} (a b : α) (h : b ∈ (pure a : PMF α).support) : b=a := by
  change b ∈ (PMF.pure a).support at h
  exact (PMF.mem_support_pure_iff a b).mp h

lemma allocate_support_extends {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (c : Coefficient p m k)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) :
    StateExtends st z.2 := by
  classical
  by_cases hd : st.dead=true
  · rw [allocate,if_pos hd] at hz
    obtain rfl := pure_support_eq_local (none,st) z hz
    exact StateExtends_refl st
  · rw [allocate,if_neg hd] at hz
    cases hc : lookupExpr st c with
    | some b =>
      rw [hc] at hz
      obtain rfl := pure_support_eq_local (some b,st) z hz
      exact StateExtends_refl st
    | none =>
      rw [hc] at hz
      by_cases hfresh : (freshCodes st).Nonempty
      · rw [dif_pos hfresh] at hz
        obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
        exact ⟨⟨[(c,b)],rfl⟩,Finset.Subset.refl _⟩
      · rw [dif_neg hfresh] at hz
        obtain rfl := pure_support_eq_local (none,{st with dead := true}) z hz
        exact ⟨List.prefix_refl _,Finset.Subset.refl _⟩


lemma freshCodes_nonempty_of_size {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k)
    (hsize : st.entries.length + st.excluded.card < 2^labelLength p.val) :
    (freshCodes st).Nonempty := by
  classical
  have heq : freshCodes st=Finset.univ \ ((st.entries.map Prod.snd).toFinset ∪ st.excluded) := by
    ext b
    simp only [freshCodes,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,
      Finset.mem_union,not_or]
  rw [heq,Finset.sdiff_nonempty]
  intro hs
  have h := Finset.card_le_card hs
  have hu := Finset.card_union_le (st.entries.map Prod.snd).toFinset st.excluded
  have hl := List.toFinset_card_le (st.entries.map Prod.snd)
  simp only [Finset.card_univ,Fintype.card_fin,List.length_map] at h hl
  omega


lemma allocate_support_shape {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (c : Coefficient p m k)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) :
    z.2.excluded=st.excluded ∧
      (z.2.entries=st.entries ∨ ∃ b ∈ freshCodes st, lookupExpr st c=none ∧ z.2.entries=st.entries ++ [(c,b)]) := by
  classical
  by_cases hd : st.dead=true
  · rw [allocate,if_pos hd] at hz
    obtain rfl := pure_support_eq_local (none,st) z hz
    exact ⟨rfl,Or.inl rfl⟩
  · rw [allocate,if_neg hd] at hz
    cases hc : lookupExpr st c with
    | some b =>
      rw [hc] at hz
      obtain rfl := pure_support_eq_local (some b,st) z hz
      exact ⟨rfl,Or.inl rfl⟩
    | none =>
      rw [hc] at hz
      by_cases hfresh : (freshCodes st).Nonempty
      · rw [dif_pos hfresh] at hz
        obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
        exact ⟨rfl,Or.inr ⟨b,(PMF.mem_support_uniformOfFinset_iff hfresh b).mp hb,rfl,rfl⟩⟩
      · rw [dif_neg hfresh] at hz
        obtain rfl := pure_support_eq_local (none,{st with dead := true}) z hz
        exact ⟨rfl,Or.inl rfl⟩

lemma allocate_support_length {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (c : Coefficient p m k)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) :
    z.2.entries.length ≤ st.entries.length+1 := by
  obtain ⟨hF,he|⟨b,hb,hc,he⟩⟩ := allocate_support_shape st c z hz
  · rw [he]
    omega
  · rw [he,List.length_append,List.length_singleton]

lemma allocate_support_WellFormed {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st) (c : Coefficient p m k)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) :
    WellFormed z.2 := by
  obtain ⟨hF,he|⟨b,hb,hc,he⟩⟩ := allocate_support_shape st c z hz
  · simpa only [WellFormed,he,hF] using hw
  · have hh := WellFormed_append st hw c b hc hb
    simpa only [WellFormed,he,hF] using hh

lemma allocate_support_live {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hl : st.dead=false) (c : Coefficient p m k)
    (hfresh : (freshCodes st).Nonempty)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) : z.2.dead=false := by
  classical
  rw [allocate,if_neg (by simp only [hl,Bool.false_eq_true,not_false_eq_true])] at hz
  cases hc : lookupExpr st c with
  | some b =>
    rw [hc] at hz
    obtain rfl := pure_support_eq_local (some b,st) z hz
    exact hl
  | none =>
    rw [hc,dif_pos hfresh] at hz
    obtain ⟨b,hb,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
    exact hl

lemma excludeOperand_card {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (x : Bits) :
    (excludeOperand st x).excluded.card ≤ st.excluded.card+1 := by
  classical
  have hs : (operandUnknownCodes st x).card ≤ 1 := by
    unfold operandUnknownCodes
    split
    · simp
    · split <;> simp
  rw [excludeOperand_excluded]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hs _)


lemma simulatorStep_support_invariant {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hw : WellFormed st) (hl : st.dead=false)
    (hsize : st.entries.length+st.excluded.card+2 < 2^labelLength p.val)
    (subtract : Bool) (x y : Bits) (z : Option Bits × SimulatorState p m k)
    (hz : z ∈ (simulatorStep st subtract x y).support) :
    StateExtends st z.2 ∧ WellFormed z.2 ∧ z.2.dead=false ∧
      z.2.entries.length ≤ st.entries.length+1 ∧ z.2.excluded.card ≤ st.excluded.card+2 := by
  classical
  let next := excludeOperand (excludeOperand st x) y
  have hNE : next.entries=st.entries := by
    dsimp only [next]
    rw [excludeOperand_entries,excludeOperand_entries]
  have hNF : next.excluded.card ≤ st.excluded.card+2 := by
    have hx := excludeOperand_card st x
    have hy := excludeOperand_card (excludeOperand st x) y
    dsimp only [next]
    omega
  have hNL : next.dead=false := by
    dsimp only [next]
    rw [excludeOperand_dead,excludeOperand_dead,hl]
  have hNW : WellFormed next := WellFormed_exclude _ (WellFormed_exclude st hw x) y
  have hNX : StateExtends st next :=
    StateExtends_trans (excludeOperand_extends st x) (excludeOperand_extends (excludeOperand st x) y)
  have hNfresh : (freshCodes next).Nonempty := freshCodes_nonempty_of_size next (by rw [hNE]; omega)
  have hbase : StateExtends st next ∧ WellFormed next ∧ next.dead=false ∧
      next.entries.length ≤ st.entries.length+1 ∧ next.excluded.card ≤ st.excluded.card+2 :=
    ⟨hNX,hNW,hNL,by rw [hNE]; omega,hNF⟩
  rw [simulatorStep,if_neg (by simp only [hl,Bool.false_eq_true,not_false_eq_true])] at hz
  cases hx : lookupOperand st x with
  | none =>
    cases hy : lookupOperand st y <;> rw [hx,hy] at hz
    all_goals
      obtain rfl := pure_support_eq_local (none,next) z hz
      exact hbase
  | some a =>
    cases hy : lookupOperand st y with
    | none =>
      rw [hx,hy] at hz
      obtain rfl := pure_support_eq_local (none,next) z hz
      exact hbase
    | some b =>
      rw [hx,hy] at hz
      obtain ⟨az,haz,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
      let c := if subtract then a-b else a+b
      refine ⟨StateExtends_trans hNX (allocate_support_extends next c az haz),
        allocate_support_WellFormed next hNW c az haz,
        allocate_support_live next hNL c hNfresh az haz,?_,?_⟩
      · have hh := allocate_support_length next c az haz
        rw [hNE] at hh
        exact hh
      · have hF := (allocate_support_shape next c az haz).1
        rw [hF]
        exact hNF


theorem simulatorTree_support_invariant {p : PrimeOrder} {m k : ℕ}
    (q : ℕ) (tree : QueryTree q) (st : SimulatorState p m k)
    (hw : WellFormed st) (hl : st.dead=false)
    (hcap : st.entries.length+st.excluded.card+3*q < 2^labelLength p.val)
    (z : Bool × SimulatorState p m k) (hz : z ∈ (simulatorTree q tree st).support) :
    StateExtends st z.2 ∧ WellFormed z.2 ∧ z.2.dead=false ∧
      z.2.entries.length ≤ st.entries.length+q ∧ z.2.excluded.card ≤ st.excluded.card+2*q := by
  classical
  induction tree generalizing st z with
  | halt bit =>
    rw [simulatorTree,if_neg (by simp only [hl,Bool.false_eq_true,not_false_eq_true])] at hz
    obtain rfl := pure_support_eq_local (bit,st) z hz
    exact ⟨StateExtends_refl st,hw,hl,by dsimp only; omega,by dsimp only; omega⟩
  | @query q subtract x y continuation ih =>
    rw [simulatorTree,if_neg (by simp only [hl,Bool.false_eq_true,not_false_eq_true])] at hz
    obtain ⟨r,hr,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
    have hs := simulatorStep_support_invariant st hw hl (by omega) subtract x y r hr
    have hnextcap : r.2.entries.length+r.2.excluded.card+3*q < 2^labelLength p.val := by
      obtain ⟨_,_,_,he,hf⟩ := hs
      omega
    have hnext := ih r.1 r.2 hs.2.1 hs.2.2.1 hnextcap z hz
    refine ⟨StateExtends_trans hs.1 hnext.1,hnext.2.1,hnext.2.2.1,?_,?_⟩
    · have hslen := hs.2.2.2.1
      have hnlen := hnext.2.2.2.1
      omega
    · have hslen := hs.2.2.2.2
      have hnlen := hnext.2.2.2.2
      omega


noncomputable def physicalNext {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits) : SimulatorState p m k :=
  let next := excludeOperand (excludeOperand st x) y
  match lookupOperand st x,lookupOperand st y with
  | some a,some b => physicalAllocate φ σ next (if subtract then a-b else a+b)
  | _,_ => next

lemma coupledTree_good_unfold {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (subtract : Bool) (x y : Bits)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (hg : ¬ stepGuess st σ x y) (hc : ¬ stepCollision φ st subtract x y) :
    coupledTree φ σ (q+1) (.query subtract x y continuation) st=
      coupledTree φ σ q
        (continuation ((⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y))
        (physicalNext φ σ st subtract x y) := by
  classical
  rw [coupledTree]
  simp only [hl,Bool.false_eq_true,ite_false,hg,hc,false_or]
  rfl

lemma physicalNext_compatible {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hσ : Compatible φ st σ) (subtract : Bool) (x y : Bits)
    (hg : ¬ stepGuess st σ x y) : Compatible φ (physicalNext φ σ st subtract x y) σ := by
  classical
  have hnext : Compatible φ (excludeOperand (excludeOperand st x) y) σ :=
    (compatible_excludeOperands φ st σ x y).mpr ⟨hσ,hg⟩
  unfold physicalNext
  cases hx : lookupOperand st x with
  | none => cases lookupOperand st y <;> exact hnext
  | some a =>
    cases hy : lookupOperand st y with
    | none => exact hnext
    | some b =>
      have he : excludeOperand (excludeOperand st x) y=st := by
        rw [excludeOperand_known st x a hx,excludeOperand_known st y b hy]
      rw [he]
      dsimp only
      unfold physicalAllocate
      cases hc : lookupExpr st (if subtract then a-b else a+b) with
      | some code => exact hσ
      | none => exact (compatible_append_iff φ st _ _ σ).mpr ⟨hσ,rfl⟩

lemma physicalNext_supported {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hσ : Compatible φ st σ) (subtract : Bool) (x y : Bits)
    (hl : st.dead=false) (hg : ¬ stepGuess st σ x y) (hcollision : ¬ stepCollision φ st subtract x y) :
    (((⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y),physicalNext φ σ st subtract x y) ∈
      (simulatorStep st subtract x y).support := by
  classical
  by_cases hi : lookupOperand st x=none ∨ lookupOperand st y=none
  · rw [physical_query_invalid st σ subtract x y hg hi,simulatorStep_invalid st subtract x y hl hi]
    have he : physicalNext φ σ st subtract x y=excludeOperand (excludeOperand st x) y := by
      unfold physicalNext
      rcases hi with hx|hy
      · rw [hx]
      · rw [hy]
        cases lookupOperand st x <;> rfl
    rw [he]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · cases hx : lookupOperand st x with
    | none => exact False.elim (hi (Or.inl hx))
    | some a =>
      cases hy : lookupOperand st y with
      | none => exact False.elim (hi (Or.inr hy))
      | some b =>
        let c := if subtract then a-b else a+b
        have he : excludeOperand (excludeOperand st x) y=st := by
          rw [excludeOperand_known st x a hx,excludeOperand_known st y b hy]
        rw [physical_query_known φ st σ hσ subtract x y a b hx hy]
        simp only [simulatorStep,hl,Bool.false_eq_true,ite_false,hx,hy,he,
          physicalNext,physicalAllocate]
        cases hc : lookupExpr st c with
        | some code =>
          have hφ := hσ.1 (c,code) (lookupExpr_some_mem st c code hc)
          simp only [c] at hc hφ
          simp only [hc,allocate,hl,Bool.false_eq_true,ite_false,hφ]
          change (some (codeBits p code),st) ∈
            ((PMF.pure (some code,st)).map fun result => (result.1.map (codeBits p),result.2)).support
          rw [PMF.pure_map]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl
        | none =>
          have hnew := fresh_value_of_no_collision φ st subtract x y a b hx hy hc hcollision
          have hbfresh := physical_new_code_fresh φ st σ hσ c hnew
          have hfresh : (freshCodes st).Nonempty := ⟨σ (fieldIndex p (φ c)),hbfresh⟩
          simp only [c] at hc
          simp only [hc,allocate,hl,Bool.false_eq_true,ite_false,dif_pos hfresh]
          apply (PMF.mem_support_map_iff _ _ _).mpr
          refine ⟨(some (σ (fieldIndex p (φ c))),{st with entries := st.entries ++ [(c,σ (fieldIndex p (φ c)))]}),?_,by simp only [hl,c,Option.map_some]⟩
          apply (PMF.mem_support_map_iff _ _ _).mpr
          exact ⟨σ (fieldIndex p (φ c)),(PMF.mem_support_uniformOfFinset_iff hfresh _).mpr hbfresh,by simp only [hl,c]⟩


lemma compatible_entries_injective {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hσ : Compatible φ st σ)
    (e f : Coefficient p m k × Code p) (he : e ∈ st.entries) (hf : f ∈ st.entries)
    (hφ : φ e.1=φ f.1) : e=f := by
  have hcode : e.2=f.2 := by rw [← hσ.1 e he,← hσ.1 f hf,hφ]
  exact List.inj_on_of_nodup_map hw.2.1 he hf hcode

lemma collision_result_new {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hσ : Compatible φ st σ)
    (a b : Coefficient p m k) (subtract : Bool) (e : Coefficient p m k × Code p)
    (he : e ∈ st.entries) (hne : (if subtract then a-b else a+b) ≠ e.1)
    (hφ : φ (if subtract then a-b else a+b)=φ e.1) :
    lookupExpr st (if subtract then a-b else a+b)=none := by
  classical
  cases hc : lookupExpr st (if subtract then a-b else a+b) with
  | none => rfl
  | some code =>
    have hcMem := lookupExpr_some_mem st _ code hc
    have hh := compatible_entries_injective φ σ st hw hσ _ e hcMem he hφ
    exact False.elim (hne (congrArg Prod.fst hh))

lemma simulatorStep_records_collision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hl : st.dead=false) (hσ : Compatible φ st σ)
    (subtract : Bool) (x y : Bits) (hc : stepCollision φ st subtract x y)
    (hfresh : (freshCodes st).Nonempty) (z : Option Bits × SimulatorState p m k)
    (hz : z ∈ (simulatorStep st subtract x y).support) : traceCollision φ z.2 := by
  classical
  obtain ⟨a,b,ha,hb,e,he,hne,hφ⟩ := hc
  have hnew := collision_result_new φ σ st hw hσ a b subtract e he hne hφ
  have hnext : excludeOperand (excludeOperand st x) y=st := by
    rw [excludeOperand_known st x a ha,excludeOperand_known st y b hb]
  simp only [simulatorStep,hl,Bool.false_eq_true,ite_false,ha,hb,hnext,allocate,hnew,dif_pos hfresh] at hz
  rw [PMF.map_comp] at hz
  obtain ⟨code,hcode,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
  exact ⟨((if subtract then a-b else a+b),code),List.mem_append_right _ (List.mem_singleton_self _),
    e,List.mem_append_left _ he,hne,hφ⟩

lemma simulatorStep_records_guess {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (σ : Encoding p.val) (hl : st.dead=false)
    (subtract : Bool) (x y : Bits) (hg : stepGuess st σ x y)
    (z : Option Bits × SimulatorState p m k) (hz : z ∈ (simulatorStep st subtract x y).support) :
    traceGuess σ z.2 := by
  classical
  have hi : lookupOperand st x=none ∨ lookupOperand st y=none := by
    cases hx : lookupOperand st x with
    | none => exact Or.inl rfl
    | some a =>
      cases hy : lookupOperand st y with
      | none => exact Or.inr rfl
      | some b => exact False.elim (stepGuess_known st σ x y a b hx hy hg)
  rw [simulatorStep_invalid st subtract x y hl hi] at hz
  obtain rfl := pure_support_eq_local (none,excludeOperand (excludeOperand st x) y) z hz
  obtain ⟨code,hcode,himage⟩ := (stepGuess_unknownCodes st σ x y).mp hg
  refine ⟨code,?_,himage⟩
  rw [excludeOperands_eq]
  exact Finset.mem_union_right _ hcode


/-- Pointwise physical output agreement off the explicitly recorded bad events. -/
theorem coupledTree_no_bad_agreement {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (q : ℕ) (tree : QueryTree q) (st : SimulatorState p m k)
    (hw : WellFormed st) (hl : st.dead=false) (hσ : Compatible φ st σ)
    (hcap : st.entries.length+st.excluded.card+3*q < 2^labelLength p.val)
    (z : Bool × SimulatorState p m k) (hz : z ∈ (coupledTree φ σ q tree st).support)
    (hnc : ¬ traceCollision φ z.2) (hng : ¬ traceGuess σ z.2) :
    tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext))=z.1 := by
  classical
  induction tree generalizing st z with
  | halt bit =>
    rw [coupledTree,if_neg (by simp only [hl,Bool.false_eq_true,not_false_eq_true])] at hz
    obtain rfl := pure_support_eq_local (bit,st) z hz
    rfl
  | @query q subtract x y continuation ih =>
    by_cases hbad : stepGuess st σ x y ∨ stepCollision φ st subtract x y
    · rw [coupledTree] at hz
      simp only [hl,Bool.false_eq_true,ite_false,if_pos hbad] at hz
      rw [simulatorTree] at hz
      simp only [hl,Bool.false_eq_true,ite_false] at hz
      obtain ⟨r,hr,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
      have hs := simulatorStep_support_invariant st hw hl (by omega) subtract x y r hr
      have hnextcap : r.2.entries.length+r.2.excluded.card+3*q < 2^labelLength p.val := by
        obtain ⟨_,_,_,he,hf⟩ := hs
        omega
      have hfinal := simulatorTree_support_invariant q (continuation r.1) r.2 hs.2.1 hs.2.2.1 hnextcap z hz
      rcases hbad with hg|hc
      · have hrecord := simulatorStep_records_guess st σ hl subtract x y hg r hr
        exact False.elim (hng (StateExtends_guess σ hfinal.1 hrecord))
      · have hfresh := freshCodes_nonempty_of_size st (by omega)
        have hrecord := simulatorStep_records_collision φ σ st hw hl hσ subtract x y hc hfresh r hr
        exact False.elim (hnc (StateExtends_collision φ hfinal.1 hrecord))
    · have hg : ¬ stepGuess st σ x y := fun h => hbad (Or.inl h)
      have hc : ¬ stepCollision φ st subtract x y := fun h => hbad (Or.inr h)
      have hsupport := physicalNext_supported φ σ st hσ subtract x y hl hg hc
      have hs := simulatorStep_support_invariant st hw hl (by omega) subtract x y _ hsupport
      dsimp only at hs
      have hnextcap : (physicalNext φ σ st subtract x y).entries.length+
          (physicalNext φ σ st subtract x y).excluded.card+3*q < 2^labelLength p.val := by
        obtain ⟨_,_,_,he,hf⟩ := hs
        omega
      rw [coupledTree_good_unfold φ σ st subtract x y continuation hl hg hc] at hz
      have hh := ih ((⟨p.val,p.property,σ⟩ : GroupContext).query subtract x y)
        (physicalNext φ σ st subtract x y) hs.2.1 hs.2.2.1
        (physicalNext_compatible φ σ st hσ subtract x y hg) hnextcap z hz hnc hng
      simpa only [QueryTree.run,Option.bind_eq_bind,Option.bind_some] using hh

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityGuessStep

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

lemma event_outer_le_one_local {α : Type*} (law : PMF α) (E : Set α) : law.toOuterMeasure E ≤ 1 := by
  have hu : law.toOuterMeasure Set.univ=1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa using law.tsum_coe
  rw [← hu]
  exact law.toOuterMeasure.mono (Set.subset_univ E)

lemma event_outer_finite_local {α : Type*} (law : PMF α) (E : Set α) : law.toOuterMeasure E ≠ ⊤ :=
  ne_of_lt ((event_outer_le_one_local law E).trans_lt ENNReal.one_lt_top)

lemma probability_le_one_local {α : Type*} (law : PMF α) (event : α → Prop) : probability law event ≤ 1 := by
  have h := ENNReal.toReal_mono (by finiteness : (1 : ENNReal) ≠ ⊤)
    (event_outer_le_one_local law {x | event x})
  simpa only [probability,ENNReal.toReal_one] using h

lemma probability_bind_finite {ι α : Type*} [Fintype ι]
    (law : PMF ι) (F : ι → PMF α) (event : α → Prop) :
    probability (law.bind F) event=∑ i, (law i).toReal*probability (F i) event := by
  unfold probability
  rw [PMF.toOuterMeasure_bind_apply,tsum_fintype,ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro i hi
    exact ENNReal.mul_ne_top (PMF.apply_ne_top law i) (event_outer_finite_local (F i) _)

lemma probability_bind_support_le {ι α : Type*} [Fintype ι]
    (law : PMF ι) (F : ι → PMF α) (event : α → Prop) (δ : ι → ℝ)
    (h : ∀ i ∈ law.support, probability (F i) event ≤ δ i) :
    probability (law.bind F) event ≤ ∑ i, (law i).toReal*δ i := by
  rw [probability_bind_finite]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hz : law i=0
  · simp only [hz,ENNReal.toReal_zero,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h i hz) ENNReal.toReal_nonneg

lemma probability_bind_bad_bound {ι α : Type*} [Fintype ι]
    (law : PMF ι) (F : ι → PMF α) (event : α → Prop) (bad : ι → Prop)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i ∈ law.support, ¬ bad i → probability (F i) event ≤ δ) :
    probability (law.bind F) event ≤ probability law bad + δ := by
  classical
  calc
    _ ≤ ∑ i, (law i).toReal*((if bad i then (1:ℝ) else 0)+δ) := by
      apply probability_bind_support_le
      intro i hi
      by_cases hb : bad i
      · rw [if_pos hb]
        exact (probability_le_one_local (F i) event).trans (by linarith)
      · simpa only [if_neg hb,zero_add] using h i hi hb
    _ = probability law bad + δ := by
      have htotal : (∑ i, (law i).toReal)=1 := by
        have ht := congrArg ENNReal.toReal law.tsum_coe
        simpa only [tsum_fintype,ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top law i),ENNReal.toReal_one] using ht
      rw [probability]
      rw [PMF.toOuterMeasure_apply,tsum_fintype]
      simp only [Set.indicator_apply,Set.mem_setOf_eq]
      rw [ENNReal.toReal_sum (fun i _ => by
        split_ifs
        · exact PMF.apply_ne_top law i
        · exact ENNReal.zero_ne_top)]
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,htotal,one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp


lemma probability_eq_zero_of_support_local {α : Type*} (law : PMF α) (E : α → Prop)
    (h : ∀ x ∈ law.support, ¬ E x) : probability law E=0 := by
  classical
  unfold probability
  have hz : law.toOuterMeasure {x | E x}=0 := by
    rw [PMF.toOuterMeasure_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
    by_cases he : E x
    · rw [if_pos he]
      by_contra hp
      exact h x hp he
    · rw [if_neg he]
  rw [hz,ENNReal.toReal_zero]

lemma fibreKernel_support_observation {ι κ : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → κ) (b : κ) (hb : Nonempty {x : ι // f x=b}) (x : ι)
    (hx : x ∈ (fibreKernel f b).support) : f x=b := by
  classical
  unfold fibreKernel at hx
  rw [dif_pos hb] at hx
  obtain ⟨y,hy,heq⟩ := (PMF.mem_support_map_iff _ _ x).mp hx
  rw [← heq]
  exact y.property

lemma uniform_fintype_irrel_local {ι : Type*} [Nonempty ι] (a b : Fintype ι) :
    @PMF.uniformOfFintype ι a inferInstance=@PMF.uniformOfFintype ι b inferInstance := by
  cases Subsingleton.elim a b
  rfl

lemma uniform_real_mass_sum {ι : Type*} [Fintype ι] (law : PMF ι) :
    (∑ i, (law i).toReal)=1 := by
  have ht := congrArg ENNReal.toReal law.tsum_coe
  simpa only [tsum_fintype,ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top law i),ENNReal.toReal_one] using ht


def operandGuess {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k)
    (σ : Encoding p.val) (x : Bits) : Prop :=
  ∃ code : Code p, readCode p x=some code ∧ lookupCode st code=none ∧ code ∈ Set.range σ

lemma probability_or_le_local {α : Type*} (law : PMF α) (E F : α → Prop) :
    probability law (fun x => E x ∨ F x) ≤ probability law E+probability law F := by
  have h := MeasureTheory.measure_union_le (μ := law.toOuterMeasure) {x | E x} {x | F x}
  have hfinite : law.toOuterMeasure {x | E x}+law.toOuterMeasure {x | F x} ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨event_outer_finite_local law _,event_outer_finite_local law _⟩
  have hr := ENNReal.toReal_mono hfinite h
  rw [ENNReal.toReal_add (event_outer_finite_local law _) (event_outer_finite_local law _)] at hr
  exact hr

lemma physical_operand_guess_bound {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (D : ℕ) (hD : 0 < D)
    (hcapacity : st.entries.length+st.excluded.card+D ≤ 2^labelLength p.val) (x : Bits) :
    probability (physicalEncodingLaw φ st h) (fun σ => operandGuess st σ x) ≤
      (p.val : ℝ)/(D : ℝ) := by
  classical
  have hnum : 0 ≤ (p.val : ℝ)/(D : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  cases hx : readCode p x with
  | none =>
    have he : (fun σ : Encoding p.val => operandGuess st σ x)=(fun _ => False) := by
      funext σ
      apply propext
      simp only [operandGuess,hx,reduceCtorEq,false_and,exists_const]
    rw [he]
    simpa only [probability,Set.setOf_false,MeasureTheory.measure_empty,ENNReal.toReal_zero] using hnum
  | some code =>
    cases hc : lookupCode st code with
    | some c =>
      have he : (fun σ : Encoding p.val => operandGuess st σ x)=(fun _ => False) := by
        funext σ
        apply propext
        simp [operandGuess,hx,hc]
      rw [he]
      simpa only [probability,Set.setOf_false,MeasureTheory.measure_empty,ENNReal.toReal_zero] using hnum
    | none =>
      have he : (fun σ : Encoding p.val => operandGuess st σ x)=(fun σ : Encoding p.val => code ∈ Set.range σ) := by
        funext σ
        apply propext
        simp [operandGuess,hx,hc]
      rw [he]
      by_cases hF : code ∈ st.excluded
      · unfold physicalEncodingLaw
        rw [probability_map_local]
        have hz : (fun σ : PhysicalCompletion φ st => code ∈ Set.range σ.val)=(fun _ => False) := by
          funext σ
          exact propext ⟨fun h => σ.property.2 code hF h,False.elim⟩
        rw [hz]
        simpa only [probability,Set.setOf_false,MeasureTheory.measure_empty,ENNReal.toReal_zero] using hnum
      · have hused := (lookupCode_none_iff st code).mp hc
        rw [physical_unknown_hit φ st h code hused hF]
        have hK : (knownPoints φ st).card ≤ st.entries.length := by
          have hh := List.toFinset_card_le (st.entries.map (fun e => fieldIndex p (φ e.1)))
          simpa only [knownPoints,List.length_map] using hh
        have hDen : D ≤ 2^labelLength p.val-(knownPoints φ st).card-st.excluded.card := by omega
        have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
        have hDenreal : (D : ℝ) ≤ ((2^labelLength p.val-(knownPoints φ st).card-st.excluded.card : ℕ) : ℝ) := by exact_mod_cast hDen
        have hDenpos : 0 < ((2^labelLength p.val-(knownPoints φ st).card-st.excluded.card : ℕ) : ℝ) := lt_of_lt_of_le hDreal hDenreal
        apply (div_le_div_iff₀ hDenpos hDreal).mpr
        have hN : ((p.val-(knownPoints φ st).card : ℕ) : ℝ) ≤ (p.val : ℝ) := by exact_mod_cast Nat.sub_le p.val (knownPoints φ st).card
        calc
          _ ≤ (p.val : ℝ)*(D : ℝ) := mul_le_mul_of_nonneg_right hN hDreal.le
          _ ≤ _ := mul_le_mul_of_nonneg_left hDenreal (Nat.cast_nonneg _)

lemma physical_step_guess_bound {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (D : ℕ) (hD : 0 < D)
    (hcapacity : st.entries.length+st.excluded.card+D ≤ 2^labelLength p.val) (x y : Bits) :
    probability (physicalEncodingLaw φ st h) (fun σ => stepGuess st σ x y) ≤
      (2 : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  have he : (fun σ : Encoding p.val => stepGuess st σ x y)=
      (fun σ => operandGuess st σ x ∨ operandGuess st σ y) := by
    funext σ
    apply propext
    constructor
    · rintro ⟨code,hread,hn,hi⟩
      rcases hread with hx|hy
      · exact Or.inl ⟨code,hx,hn,hi⟩
      · exact Or.inr ⟨code,hy,hn,hi⟩
    · rintro (⟨code,hx,hn,hi⟩|⟨code,hy,hn,hi⟩)
      · exact ⟨code,Or.inl hx,hn,hi⟩
      · exact ⟨code,Or.inr hy,hn,hi⟩
  rw [he]
  calc
    _ ≤ _ := probability_or_le_local _ _ _
    _ ≤ (p.val : ℝ)/(D : ℝ)+(p.val : ℝ)/(D : ℝ) :=
      add_le_add (physical_operand_guess_bound φ st h D hD hcapacity x)
        (physical_operand_guess_bound φ st h D hD hcapacity y)
    _ = _ := by ring

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityGuessTrace

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

def guessWithoutCollision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (z : Encoding p.val × (Bool × SimulatorState p m k)) : Prop :=
  traceGuess z.1 z.2.2 ∧ ¬ traceCollision φ z.2.2

lemma physicalEncodingLaw_support_compatible {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (σ : Encoding p.val)
    (hσ : σ ∈ (physicalEncodingLaw φ st h).support) : Compatible φ st σ := by
  classical
  unfold physicalEncodingLaw at hσ
  obtain ⟨x,hx,heq⟩ := (PMF.mem_support_map_iff _ _ σ).mp hσ
  rw [← heq]
  exact x.property

lemma coupledTreeLaw_support_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (q : ℕ) (tree : QueryTree q)
    (z : Encoding p.val × (Bool × SimulatorState p m k)) :
    z ∈ (coupledTreeLaw φ st h q tree).support ↔
      z.1 ∈ (physicalEncodingLaw φ st h).support ∧ z.2 ∈ (coupledTree φ z.1 q tree st).support := by
  unfold coupledTreeLaw
  constructor
  · intro hz
    obtain ⟨σ,hσ,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
    obtain ⟨out,hout,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
    exact ⟨hσ,hout⟩
  · rintro ⟨hσ,hout⟩
    apply (PMF.mem_support_bind_iff _ _ z).mpr
    exact ⟨z.1,hσ,(PMF.mem_support_map_iff _ _ z).mpr ⟨z.2,hout,rfl⟩⟩

lemma simulatorTree_collision_record {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hl : st.dead=false) (hσ : Compatible φ st σ)
    (hcap : st.entries.length+st.excluded.card+3*(q+1) < 2^labelLength p.val)
    (subtract : Bool) (x y : Bits) (continuation : Option Bits → QueryTree q)
    (hc : stepCollision φ st subtract x y) (z : Bool × SimulatorState p m k)
    (hz : z ∈ (simulatorTree (q+1) (.query subtract x y continuation) st).support) :
    traceCollision φ z.2 := by
  classical
  rw [simulatorTree] at hz
  simp only [hl,Bool.false_eq_true,ite_false] at hz
  obtain ⟨r,hr,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
  have hs := simulatorStep_support_invariant st hw hl (by omega) subtract x y r hr
  have hnextcap : r.2.entries.length+r.2.excluded.card+3*q < 2^labelLength p.val := by
    obtain ⟨_,_,_,he,hf⟩ := hs
    omega
  have hfinal := simulatorTree_support_invariant q (continuation r.1) r.2 hs.2.1 hs.2.2.1 hnextcap z hz
  have hfresh := freshCodes_nonempty_of_size st (by omega)
  have hrecord := simulatorStep_records_collision φ σ st hw hl hσ subtract x y hc hfresh r hr
  exact StateExtends_collision φ hfinal.1 hrecord

lemma coupledTreeLaw_collision_zero {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (hw : WellFormed st) (hl : st.dead=false)
    (hcap : st.entries.length+st.excluded.card+3*(q+1) < 2^labelLength p.val)
    (subtract : Bool) (x y : Bits) (continuation : Option Bits → QueryTree q)
    (hc : stepCollision φ st subtract x y) :
    probability (coupledTreeLaw φ st h (q+1) (.query subtract x y continuation))
      (guessWithoutCollision φ)=0 := by
  classical
  apply probability_eq_zero_of_support_local
  intro z hz hevent
  obtain ⟨hσ,hout⟩ := (coupledTreeLaw_support_iff φ st h _ _ z).mp hz
  have hcomp := physicalEncodingLaw_support_compatible φ st h z.1 hσ
  rw [coupledTree] at hout
  simp only [hl,Bool.false_eq_true,ite_false,hc,or_true,ite_true] at hout
  exact hevent.2 (simulatorTree_collision_record φ z.1 st hw hl hcomp hcap subtract x y continuation hc z.2 hout)

lemma coupledTreeLaw_halt_guess_zero {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (h : Nonempty (PhysicalCompletion φ st)) (hl : st.dead=false) (bit : Bool) :
    probability (coupledTreeLaw φ st h q (.halt bit)) (guessWithoutCollision φ)=0 := by
  classical
  apply probability_eq_zero_of_support_local
  intro z hz hevent
  obtain ⟨hσ,hout⟩ := (coupledTreeLaw_support_iff φ st h _ _ z).mp hz
  have hcomp := physicalEncodingLaw_support_compatible φ st h z.1 hσ
  rw [coupledTree] at hout
  simp only [hl,Bool.false_eq_true,ite_false] at hout
  have heq := pure_support_eq_local (bit,st) z.2 hout
  have hstate : z.2.2=st := congrArg Prod.snd heq
  obtain ⟨code,hcode,himage⟩ := hevent.1
  rw [hstate] at hcode
  exact hcomp.2 code hcode himage


lemma probability_bind_const_bound {ι α : Type*} [Fintype ι]
    (law : PMF ι) (F : ι → PMF α) (E : α → Prop) (δ : ℝ)
    (h : ∀ i ∈ law.support, probability (F i) E ≤ δ) :
    probability (law.bind F) E ≤ δ := by
  calc
    _ ≤ ∑ i, (law i).toReal*δ := probability_bind_support_le law F E (fun _ => δ) h
    _ = _ := by rw [← Finset.sum_mul,uniform_real_mass_sum,one_mul]

lemma probability_uniform_fibre_bound {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) (g : ι → PMF α) (E : α → Prop) (δ : ℝ)
    (h : ∀ b (hb : Nonempty {x : ι // f x=b}), probability ((fibreKernel f b).bind g) E ≤ δ) :
    probability ((PMF.uniformOfFintype ι).bind g) E ≤ δ := by
  classical
  rw [uniform_fibre_bind f g]
  apply probability_bind_const_bound
  intro b hb
  obtain ⟨x,hx,hxb⟩ := (PMF.mem_support_map_iff f (PMF.uniformOfFintype ι) b).mp hb
  exact h b ⟨⟨x,hxb⟩⟩

lemma probability_uniform_fibre_bad_bound {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [DecidableEq κ] (f : ι → κ) (g : ι → PMF α) (E : α → Prop)
    (bad : κ → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ b (hb : Nonempty {x : ι // f x=b}), ¬ bad b →
      probability ((fibreKernel f b).bind g) E ≤ δ) :
    probability ((PMF.uniformOfFintype ι).bind g) E ≤
      probability ((PMF.uniformOfFintype ι).map f) bad+δ := by
  classical
  rw [uniform_fibre_bind f g]
  apply probability_bind_bad_bound _ _ _ _ δ hδ
  intro b hb hgood
  obtain ⟨x,hx,hxb⟩ := (PMF.mem_support_map_iff f (PMF.uniformOfFintype ι) b).mp hb
  exact h b ⟨⟨x,hxb⟩⟩ hgood

lemma coupledTreeLaw_existing_eq {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b) (code : Code p)
    (hc : lookupExpr st (if subtract then a-b else a+b)=some code)
    (hcollision : ¬ stepCollision φ st subtract x y) :
    coupledTreeLaw φ st h (q+1) (.query subtract x y continuation)=
      coupledTreeLaw φ st h q (continuation (some (codeBits p code))) := by
  unfold coupledTreeLaw
  apply bind_congr_support_local
  intro σ hσ
  have hcomp := physicalEncodingLaw_support_compatible φ st h σ hσ
  rw [coupledTree_known_existing φ st σ hcomp subtract x y a b continuation hl ha hb code hc hcollision]


lemma coupledTreeLaw_invalid_guess_step {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (continuation : Option Bits → QueryTree q)
    (hl : st.dead=false) (hi : lookupOperand st x=none ∨ lookupOperand st y=none)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (ih : ∀ hnext : Nonempty (PhysicalCompletion φ (excludeOperand (excludeOperand st x) y)),
      probability (coupledTreeLaw φ (excludeOperand (excludeOperand st x) y) hnext q (continuation none))
        (guessWithoutCollision φ) ≤ δ) :
    probability (coupledTreeLaw φ st h (q+1) (.query subtract x y continuation)) (guessWithoutCollision φ) ≤
      probability (physicalEncodingLaw φ st h) (fun σ => stepGuess st σ x y)+δ := by
  classical
  let next := excludeOperand (excludeOperand st x) y
  letI : Nonempty (PhysicalCompletion φ st) := h
  let obs := fun σ : PhysicalCompletion φ st => decide (¬ stepGuess st σ.val x y)
  have hBad : probability ((PMF.uniformOfFintype (PhysicalCompletion φ st)).map obs) (fun b => b=false)=
      probability (physicalEncodingLaw φ st h) (fun σ => stepGuess st σ x y) := by
    rw [probability_map_local]
    unfold physicalEncodingLaw
    rw [probability_map_local]
    congr 1
    funext σ
    exact propext (by simp only [obs,decide_eq_false_iff_not,not_not])
  rw [← hBad]
  unfold coupledTreeLaw physicalEncodingLaw
  rw [PMF.bind_map]
  apply probability_uniform_fibre_bad_bound obs _ _ (fun b => b=false) δ hδ
  intro b hb hgood
  cases b with
  | false => exact False.elim (hgood rfl)
  | true =>
    let σ₀ := Classical.choice hb
    have hg₀ : ¬ stepGuess st σ₀.val.val x y := of_decide_eq_true σ₀.property
    have hnext : Nonempty (PhysicalCompletion φ next) :=
      ⟨⟨σ₀.val.val,(compatible_excludeOperands φ st σ₀.val.val x y).mpr ⟨σ₀.val.property,hg₀⟩⟩⟩
    have hkernel : (fibreKernel obs true).map Subtype.val=physicalEncodingLaw φ next hnext := by
      apply uniform_refinement (Compatible φ st) (Compatible φ next)
        (fun σ => decide (¬ stepGuess st σ x y)) true h hnext
      intro σ
      simpa only [decide_eq_true_eq] using compatible_excludeOperands φ st σ x y
    have hbody : (fibreKernel obs true).bind
        (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val (q+1) (.query subtract x y continuation) st).map
          (fun out => (σ.val,out))) =
        (fibreKernel obs true).bind
        (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val q (continuation none) next).map
          (fun out => (σ.val,out))) := by
      apply bind_congr_support_local
      intro σ hσ
      have hobs := fibreKernel_support_observation obs true hb σ hσ
      have hg : ¬ stepGuess st σ.val x y := of_decide_eq_true hobs
      rw [coupledTree_invalid_good φ st σ.val subtract x y continuation hl hi hg]
    have hh := congrArg (fun law : PMF (Encoding p.val) => law.bind fun σ =>
      (coupledTree φ σ q (continuation none) next).map (fun out => (σ,out))) hkernel
    rw [PMF.bind_map] at hh
    have hLaw : (fibreKernel obs true).bind
        (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val (q+1) (.query subtract x y continuation) st).map
          (fun out => (σ.val,out))) = coupledTreeLaw φ next hnext q (continuation none) := by
      exact hbody.trans (by simpa only [coupledTreeLaw,Function.comp_def] using hh)
    simp only [Function.comp_def]
    rw [hLaw]
    exact ih hnext


lemma coupledTreeLaw_fresh_guess_step {p : PrimeOrder} {m k q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st))
    (subtract : Bool) (x y : Bits) (a b : Coefficient p m k)
    (continuation : Option Bits → QueryTree q) (hl : st.dead=false)
    (ha : lookupOperand st x=some a) (hb : lookupOperand st y=some b)
    (hc : lookupExpr st (if subtract then a-b else a+b)=none)
    (hcollision : ¬ stepCollision φ st subtract x y) (δ : ℝ)
    (ih : ∀ code : Code p, code ∈ freshCodes st →
      ∀ hnext : Nonempty (PhysicalCompletion φ {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]}),
      probability (coupledTreeLaw φ {st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]}
        hnext q (continuation (some (codeBits p code)))) (guessWithoutCollision φ) ≤ δ) :
    probability (coupledTreeLaw φ st h (q+1) (.query subtract x y continuation)) (guessWithoutCollision φ) ≤ δ := by
  classical
  let c := if subtract then a-b else a+b
  have hnew := fresh_value_of_no_collision φ st subtract x y a b ha hb hc hcollision
  letI : Nonempty (PhysicalCompletion φ st) := h
  let obs := fun σ : PhysicalCompletion φ st => σ.val (fieldIndex p (φ c))
  unfold coupledTreeLaw physicalEncodingLaw
  rw [PMF.bind_map]
  apply probability_uniform_fibre_bound obs
  intro code hcode
  let σ₀ := Classical.choice hcode
  have hbfresh : code ∈ freshCodes st := by
    rw [← σ₀.property]
    exact physical_new_code_fresh φ st σ₀.val.val σ₀.val.property c hnew
  have hnext : Nonempty (PhysicalCompletion φ {st with entries := st.entries ++ [(c,code)]}) :=
    ⟨⟨σ₀.val.val,(compatible_append_iff φ st c code σ₀.val.val).mpr ⟨σ₀.val.property,σ₀.property⟩⟩⟩
  have hkernel := physical_reveal_condition φ st h c code hnext
  have hbody : (fibreKernel obs code).bind
      (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val (q+1) (.query subtract x y continuation) st).map
        (fun out => (σ.val,out))) =
      (fibreKernel obs code).bind
      (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val q (continuation (some (codeBits p code)))
        {st with entries := st.entries ++ [(c,code)]}).map (fun out => (σ.val,out))) := by
    apply bind_congr_support_local
    intro σ hσ
    have hobs := fibreKernel_support_observation obs code hcode σ hσ
    rw [coupledTree_known_fresh φ st σ.val σ.property subtract x y a b continuation hl ha hb hc hcollision]
    change σ.val (fieldIndex p (φ (if subtract then a-b else a+b)))=code at hobs
    rw [hobs]
  have hh := congrArg (fun law : PMF (Encoding p.val) => law.bind fun σ =>
    (coupledTree φ σ q (continuation (some (codeBits p code)))
      {st with entries := st.entries ++ [(c,code)]}).map (fun out => (σ,out))) hkernel
  rw [PMF.bind_map] at hh
  have hLaw : (fibreKernel obs code).bind
      (fun σ : PhysicalCompletion φ st => (coupledTree φ σ.val (q+1) (.query subtract x y continuation) st).map
        (fun out => (σ.val,out))) =
      coupledTreeLaw φ {st with entries := st.entries ++ [(c,code)]} hnext q (continuation (some (codeBits p code))) := by
    exact hbody.trans (by simpa only [coupledTreeLaw,Function.comp_def] using hh)
  simp only [Function.comp_def]
  rw [hLaw]
  exact ih code hbfresh hnext


/-- First unseen-valid-guess bound for the explicit conditioned traversal.
The positive integer D remains a lower bound on free labels throughout. -/
theorem coupledTree_guess_rate {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (D : ℕ) (hD : 0 < D)
    (q : ℕ) (tree : QueryTree q) (st : SimulatorState p m k)
    (hw : WellFormed st) (hl : st.dead=false) (h : Nonempty (PhysicalCompletion φ st))
    (hcapacity : st.entries.length+st.excluded.card+3*q+D ≤ 2^labelLength p.val) :
    probability (coupledTreeLaw φ st h q tree) (guessWithoutCollision φ) ≤
      (2 : ℝ)*(q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  classical
  induction tree generalizing st with
  | halt bit =>
    rw [coupledTreeLaw_halt_guess_zero φ st h hl bit]
    positivity
  | @query q subtract x y continuation ih =>
    have hrate : (2 : ℝ)*(q : ℝ)*(p.val : ℝ)/(D : ℝ) ≤
        (2 : ℝ)*((q+1 : ℕ) : ℝ)*(p.val : ℝ)/(D : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simp only [Nat.cast_add,Nat.cast_one]
      nlinarith [show (0 : ℝ) ≤ (p.val : ℝ) from Nat.cast_nonneg _]
    by_cases hcollision : stepCollision φ st subtract x y
    · rw [coupledTreeLaw_collision_zero φ st h hw hl (by omega) subtract x y continuation hcollision]
      positivity
    · by_cases hi : lookupOperand st x=none ∨ lookupOperand st y=none
      · have hbranch := coupledTreeLaw_invalid_guess_step φ st h subtract x y continuation hl hi
          ((2 : ℝ)*(q : ℝ)*(p.val : ℝ)/(D : ℝ)) (by positivity) (by
            intro hnext
            have hNF : (excludeOperand (excludeOperand st x) y).excluded.card ≤ st.excluded.card+2 := by
              have hx := excludeOperand_card st x
              have hy := excludeOperand_card (excludeOperand st x) y
              omega
            have hNE : (excludeOperand (excludeOperand st x) y).entries=st.entries := by
              rw [excludeOperand_entries,excludeOperand_entries]
            have hNL : (excludeOperand (excludeOperand st x) y).dead=false := by
              rw [excludeOperand_dead,excludeOperand_dead,hl]
            have hnextcap : (excludeOperand (excludeOperand st x) y).entries.length+
                (excludeOperand (excludeOperand st x) y).excluded.card+3*q+D ≤ 2^labelLength p.val := by
              rw [hNE]
              omega
            exact ih none _ (WellFormed_exclude _ (WellFormed_exclude st hw x) y) hNL hnext hnextcap)
        calc
          _ ≤ _ := hbranch
          _ ≤ (2 : ℝ)*(p.val : ℝ)/(D : ℝ)+(2 : ℝ)*(q : ℝ)*(p.val : ℝ)/(D : ℝ) :=
            by
              have hh := physical_step_guess_bound φ st h D hD (by omega) x y
              linarith
          _ = _ := by simp only [Nat.cast_add,Nat.cast_one]; ring
      · cases hx : lookupOperand st x with
        | none => exact False.elim (hi (Or.inl (by simp only [hx])))
        | some a =>
          cases hy : lookupOperand st y with
          | none => exact False.elim (hi (Or.inr (by simp only [hy])))
          | some b =>
            cases hc : lookupExpr st (if subtract then a-b else a+b) with
            | some code =>
              rw [coupledTreeLaw_existing_eq φ st h subtract x y a b continuation hl hx hy code hc hcollision]
              exact (ih (some (codeBits p code)) st hw hl h (by omega)).trans hrate
            | none =>
              apply le_trans (coupledTreeLaw_fresh_guess_step φ st h subtract x y a b continuation hl hx hy hc hcollision
                ((2 : ℝ)*(q : ℝ)*(p.val : ℝ)/(D : ℝ)) (by
                  intro code hbfresh hnext
                  have hnextcap :
                      ({st with entries := st.entries ++ [((if subtract then a-b else a+b),code)]} : SimulatorState p m k).entries.length+
                      st.excluded.card+3*q+D ≤ 2^labelLength p.val := by
                    simp only [List.length_append,List.length_singleton]
                    omega
                  exact ih (some (codeBits p code)) _ (WellFormed_append st hw _ code hc hbfresh) hl hnext hnextcap)) hrate

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.FiniteUniformConditioningGeneral

namespace GenericGroupWE.Main.GenericSecurityProof
theorem uniform_fibre_recombine_general {ι κ : Type*} [Fintype ι]
    [Nonempty ι] (f : ι → κ) :
    ((PMF.uniformOfFintype ι).map f).bind (fibreKernel f) = PMF.uniformOfFintype ι := by
  classical
  apply PMF.ext
  intro x
  rw [PMF.bind_apply, PMF.uniformOfFintype_apply]
  have hzero : ∀ o : κ, o ≠ f x →
      ((PMF.uniformOfFintype ι).map f) o * fibreKernel f o x = 0 := by
    intro o ho
    by_cases hn : Nonempty {y : ι // f y=o}
    · rw [fibreKernel_apply f o hn x, if_neg (Ne.symm ho), mul_zero]
    · letI : IsEmpty {y : ι // f y=o} := not_nonempty_iff.mp hn
      rw [uniform_map_mass]
      simp
  rw [tsum_eq_single (f x) hzero]
  letI : Nonempty {y : ι // f y=f x} := ⟨⟨x,rfl⟩⟩
  have hF : (Nat.card {y : ι // f y=f x} : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := {y : ι // f y=f x})).ne'
  rw [uniform_map_mass, fibreKernel_apply f (f x) inferInstance x, if_pos rfl]
  rw [← Nat.card_eq_fintype_card]
  calc
    (Nat.card {y : ι // f y=f x} : ENNReal)/(Nat.card ι : ENNReal) *
        (Nat.card {y : ι // f y=f x} : ENNReal)⁻¹ =
      (Nat.card ι : ENNReal)⁻¹ * ((Nat.card {y : ι // f y=f x} : ENNReal) *
        (Nat.card {y : ι // f y=f x} : ENNReal)⁻¹) := by
      simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ = _ := by rw [ENNReal.mul_inv_cancel hF (by finiteness), mul_one]


end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityInitialPublic

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

def emptySimulatorState (p : PrimeOrder) (m k : ℕ) : SimulatorState p m k := ⟨[],∅,false⟩

noncomputable def initialSimulatorLaw (p : PrimeOrder) (m k : ℕ) : PMF (SimulatorState p m k) :=
  allocateForms (initialForms p m k) (emptySimulatorState p m k)

noncomputable def physicalForms {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val) :
    List (Coefficient p m k) → SimulatorState p m k → SimulatorState p m k
  | [],st => st
  | c::cs,st => physicalForms φ σ cs (physicalAllocate φ σ st c)

def InitialAssigned {p : PrimeOrder} {m k : ℕ} (st : SimulatorState p m k) : Prop :=
  ∀ c ∈ initialForms p m k, ∃ code : Code p, (c,code) ∈ st.entries

lemma initialForms_length (p : PrimeOrder) (m k : ℕ) : (initialForms p m k).length=m+k+1 := by
  simp only [initialForms,List.length_append,List.length_singleton,List.length_ofFn]
  omega

lemma sCoefficient_injective (p : PrimeOrder) (m k : ℕ) : Function.Injective (sCoefficient p m k) := by
  classical
  intro i j he
  by_contra hij
  have hc := congrArg (fun c : Coefficient p m k => c.2.1 i) he
  simpa [sCoefficient,Pi.single_apply,hij,Ne.symm hij] using hc

lemma zCoefficient_injective (p : PrimeOrder) (m k : ℕ) : Function.Injective (zCoefficient p m k) := by
  classical
  intro i j he
  by_contra hij
  have hc := congrArg (fun c : Coefficient p m k => c.2.2 i) he
  simpa [zCoefficient,Pi.single_apply,hij,Ne.symm hij] using hc

lemma initialForms_nodup (p : PrimeOrder) (m k : ℕ) : (initialForms p m k).Nodup := by
  classical
  have hs : (List.ofFn (sCoefficient p m k)).Nodup := List.nodup_ofFn.mpr (sCoefficient_injective p m k)
  have hz : (List.ofFn (zCoefficient p m k)).Nodup := List.nodup_ofFn.mpr (zCoefficient_injective p m k)
  have hsz : (List.ofFn (sCoefficient p m k) ++ List.ofFn (zCoefficient p m k)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hs,hz,?_⟩
    intro a ha b hb hab
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
    have hc := congrArg (fun c : Coefficient p m k => c.2.1 i) hab
    simpa [sCoefficient,zCoefficient,Pi.single_apply] using hc
  have hfull : ([oneCoefficient p m k] ++
      (List.ofFn (sCoefficient p m k) ++ List.ofFn (zCoefficient p m k))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨by simp,hsz,?_⟩
    intro a ha b hb hab
    obtain rfl := List.mem_singleton.mp ha
    rcases List.mem_append.mp hb with hb|hb
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
      simpa [oneCoefficient,sCoefficient] using congrArg Prod.fst hab
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
      simpa [oneCoefficient,zCoefficient] using congrArg Prod.fst hab
  simpa only [initialForms,List.append_assoc] using hfull

lemma InitialAssigned_collision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (ha : InitialAssigned st) (hc : ¬ ((initialForms p m k).map φ).Nodup) : traceCollision φ st := by
  classical
  by_contra hno
  apply hc
  apply (List.nodup_map_iff_inj_on (initialForms_nodup p m k)).mpr
  intro a ha' b hb' hab
  by_contra hne
  obtain ⟨codeA,hA⟩ := ha a ha'
  obtain ⟨codeB,hB⟩ := ha b hb'
  exact hno ⟨(a,codeA),hA,(b,codeB),hB,hne,hab⟩

lemma compatible_empty {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val) :
    Compatible φ (emptySimulatorState p m k) σ := by
  simp [Compatible,emptySimulatorState]

noncomputable def emptyCompletionEquiv {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) :
    PhysicalCompletion φ (emptySimulatorState p m k) ≃ Encoding p.val where
  toFun := Subtype.val
  invFun σ := ⟨σ,compatible_empty φ σ⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma empty_completion_nonempty {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) :
    Nonempty (PhysicalCompletion φ (emptySimulatorState p m k)) :=
  Nonempty.map (emptyCompletionEquiv φ).symm inferInstance

lemma physical_empty_uniform {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) :
    physicalEncodingLaw φ (emptySimulatorState p m k) (empty_completion_nonempty φ)=
      PMF.uniformOfFintype (Encoding p.val) := by
  classical
  letI := empty_completion_nonempty φ
  unfold physicalEncodingLaw
  exact uniform_equiv_map (emptyCompletionEquiv φ)


noncomputable def physicalPublic {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val) : Bits :=
  let Γ : GroupContext := ⟨p.val,p.property,σ⟩
  pack [publicContext (some Γ),replyBits (some (pack [Γ.generator,
    pack (List.ofFn fun i : Fin m => encodeField σ (φ (sCoefficient p m k i))),
    pack (List.ofFn fun j : Fin k => encodeField σ (φ (zCoefficient p m k j)))]))]

lemma code_one_generator (p : PrimeOrder) (σ : Encoding p.val) :
    codeBits p (σ (fieldIndex p (1 : ZMod p.val)))=(⟨p.val,p.property,σ⟩ : GroupContext).generator := by
  change label σ ⟨(1 : ZMod p.val).val,ZMod.val_lt _⟩=label σ ⟨1,p.property.one_lt⟩
  apply congrArg (label σ)
  apply Fin.ext
  simp [ZMod.val_one,Nat.mod_eq_of_lt p.property.one_lt]

lemma assigned_form_encode {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hσ : Compatible φ st σ)
    (c : Coefficient p m k) (hc : ∃ code : Code p, (c,code) ∈ st.entries) :
    ((lookupExpr st c).map (codeBits p)).getD []=encodeField σ (φ c) := by
  obtain ⟨code,hcode⟩ := hc
  have hl := lookupExpr_of_mem st hw c code hcode
  simp only [hl,Option.map_some,Option.getD_some]
  have he := hσ.1 (c,code) hcode
  change codeBits p code=codeBits p (σ (fieldIndex p (φ c)))
  rw [he]

lemma simulator_public_physical {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (st : SimulatorState p m k) (hw : WellFormed st) (hσ : Compatible φ st σ)
    (ha : InitialAssigned st) (hOne : φ (oneCoefficient p m k)=1) :
    simulatorPublic st=physicalPublic φ σ := by
  classical
  have hG : ((lookupExpr st (oneCoefficient p m k)).map (codeBits p)).getD []=
      (⟨p.val,p.property,σ⟩ : GroupContext).generator := by
    rw [assigned_form_encode φ σ st hw hσ _ (ha _ (by simp [initialForms])),hOne]
    exact code_one_generator p σ
  have hS (i : Fin m) : ((lookupExpr st (sCoefficient p m k i)).map (codeBits p)).getD []=
      encodeField σ (φ (sCoefficient p m k i)) := by
    apply assigned_form_encode φ σ st hw hσ
    apply ha
    simp only [initialForms,List.mem_append,List.mem_singleton,List.mem_ofFn]
    exact Or.inl (Or.inr ⟨i,rfl⟩)
  have hZ (j : Fin k) : ((lookupExpr st (zCoefficient p m k j)).map (codeBits p)).getD []=
      encodeField σ (φ (zCoefficient p m k j)) := by
    apply assigned_form_encode φ σ st hw hσ
    apply ha
    simp only [initialForms,List.mem_append,List.mem_singleton,List.mem_ofFn]
    exact Or.inr ⟨j,rfl⟩
  simp only [simulatorPublic,physicalPublic,hG,hS,hZ,publicContext]


lemma evaluation_one (p : PrimeOrder) (m k : ℕ)
    (s : Fin m → ZMod p.val) (y : Fin k → ZMod p.val) :
    evaluation p m k s y (oneCoefficient p m k)=1 := by
  simp [evaluation,oneCoefficient]

lemma evaluation_s (p : PrimeOrder) (m k : ℕ)
    (s : Fin m → ZMod p.val) (y : Fin k → ZMod p.val) (i : Fin m) :
    evaluation p m k s y (sCoefficient p m k i)=s i := by
  classical
  simp [evaluation,sCoefficient,Pi.single_apply]

lemma evaluation_z (p : PrimeOrder) (m k : ℕ)
    (s : Fin m → ZMod p.val) (y : Fin k → ZMod p.val) (j : Fin k) :
    evaluation p m k s y (zCoefficient p m k j)=y j := by
  classical
  simp [evaluation,zCoefficient,Pi.single_apply]

lemma coordinate_public_evaluation {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
    (t : Fin B.k → ZMod p.val) (message : Bool) :
    (coordinateCiphertext B σ s r t message).public=
      physicalPublic (evaluation p m B.k s (fun j =>
        if message then t j else ∑ i : Fin m, ∑ l : Fin m,
          s i*B.matrices j i l*(r l : ZMod p.val))) σ := by
  simp only [coordinateCiphertext,Ciphertext.public,physicalPublic,evaluation_s,evaluation_z]

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityInitialLabels

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

lemma physicalForms_compatible {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (forms : List (Coefficient p m k)) (st : SimulatorState p m k) (hσ : Compatible φ st σ) :
    Compatible φ (physicalForms φ σ forms st) σ := by
  classical
  induction forms generalizing st with
  | nil => exact hσ
  | cons c cs ih =>
    apply ih
    unfold physicalAllocate
    cases lookupExpr st c with
    | some code => exact hσ
    | none => exact (compatible_append_iff φ st c _ σ).mpr ⟨hσ,rfl⟩

/-- Repeated physical forward reveals have exactly the finite lazy allocation law
when the listed evaluated values are new and pairwise distinct. -/
theorem physicalForms_forward_law {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (forms : List (Coefficient p m k))
    (st : SimulatorState p m k) (h : Nonempty (PhysicalCompletion φ st)) (hl : st.dead=false)
    (hnodup : (forms.map φ).Nodup)
    (hnew : ∀ c ∈ forms, ∀ e ∈ st.entries, φ c ≠ φ e.1) :
    (physicalEncodingLaw φ st h).map (fun σ => physicalForms φ σ forms st)=allocateForms forms st := by
  classical
  induction forms generalizing st with
  | nil =>
    change (physicalEncodingLaw φ st h).map (fun _ => st)=PMF.pure st
    exact PMF.map_const _ _
  | cons c cs ih =>
    have hphi : φ c ∉ cs.map φ ∧ (cs.map φ).Nodup := by
      simpa only [List.map_cons,List.nodup_cons] using hnodup
    have hnewc : ∀ e ∈ st.entries, φ c ≠ φ e.1 := hnew c List.mem_cons_self
    have hlookup : lookupExpr st c=none := by
      cases hc : lookupExpr st c with
      | none => rfl
      | some code => exact False.elim (hnewc (c,code) (lookupExpr_some_mem st c code hc) rfl)
    have hfresh := freshCodes_nonempty_physical φ st h c hnewc
    letI : Nonempty (PhysicalCompletion φ st) := h
    rw [allocateForms]
    simp only [allocate,hl,Bool.false_eq_true,ite_false,hlookup,dif_pos hfresh]
    rw [PMF.bind_map]
    rw [← fresh_physical_forward φ st h c hnewc hfresh]
    unfold physicalEncodingLaw
    rw [PMF.map_comp,PMF.map_comp]
    rw [← PMF.bind_pure_comp]
    apply uniform_bind_compare_fibres (fun σ : PhysicalCompletion φ st => σ.val (fieldIndex p (φ c)))
    intro code hcode
    let σ₀ := Classical.choice hcode
    have hnext : Nonempty (PhysicalCompletion φ {st with entries := st.entries ++ [(c,code)]}) :=
      ⟨⟨σ₀.val.val,(compatible_append_iff φ st c code σ₀.val.val).mpr ⟨σ₀.val.property,σ₀.property⟩⟩⟩
    have hnewtail : ∀ d ∈ cs, ∀ e ∈ ({st with entries := st.entries ++ [(c,code)]} : SimulatorState p m k).entries,
        φ d ≠ φ e.1 := by
      intro d hd e he
      rcases List.mem_append.mp he with he|he
      · exact hnew d (List.mem_cons_of_mem c hd) e he
      · obtain rfl := List.mem_singleton.mp he
        intro hdc
        exact hphi.1 (List.mem_map.mpr ⟨d,hd,hdc⟩)
    have he (σ : {σ : PhysicalCompletion φ st // σ.val (fieldIndex p (φ c))=code}) :
        physicalForms φ σ.val.val (c::cs) st=
          physicalForms φ σ.val.val cs {st with entries := st.entries ++ [(c,code)]} := by
      simp only [physicalForms,physicalAllocate,hlookup]
      rw [σ.property]
    simp only [Function.comp_def]
    simp_rw [he]
    change (PMF.uniformOfFintype {σ : PhysicalCompletion φ st // σ.val (fieldIndex p (φ c))=code}).map
      (fun σ => physicalForms φ σ.val.val cs {st with entries := st.entries ++ [(c,code)]}) = _
    have hkernel := physical_reveal_condition φ st h c code hnext
    unfold fibreKernel at hkernel
    rw [dif_pos hcode,PMF.map_comp] at hkernel
    have hh := congrArg (fun law : PMF (Encoding p.val) => law.map
      (fun σ => physicalForms φ σ cs {st with entries := st.entries ++ [(c,code)]})) hkernel
    rw [PMF.map_comp] at hh
    calc
      _ = (physicalEncodingLaw φ {st with entries := st.entries ++ [(c,code)]} hnext).map
          (fun σ => physicalForms φ σ cs {st with entries := st.entries ++ [(c,code)]}) := by
        apply PMF.ext
        intro out
        have hp := congrArg (fun law : PMF (SimulatorState p m k) => law out) hh
        simpa only [PMF.map_apply,PMF.uniformOfFintype_apply,← Nat.card_eq_fintype_card,
          Function.comp_def] using hp
      _ = _ := by simpa only [hl] using ih _ hnext hl hphi.2 hnewtail


lemma allocate_support_fresh_shape {p : PrimeOrder} {m k : ℕ}
    (st : SimulatorState p m k) (hl : st.dead=false) (c : Coefficient p m k)
    (hc : lookupExpr st c=none) (hfresh : (freshCodes st).Nonempty)
    (z : Option (Code p) × SimulatorState p m k) (hz : z ∈ (allocate st c).support) :
    ∃ code ∈ freshCodes st, z=(some code,{st with entries := st.entries ++ [(c,code)]}) := by
  classical
  simp only [allocate,hl,Bool.false_eq_true,ite_false,hc,dif_pos hfresh] at hz
  obtain ⟨code,hcode,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
  exact ⟨code,(PMF.mem_support_uniformOfFinset_iff hfresh code).mp hcode,by simp only [hl]⟩

theorem allocateForms_support_keys {p : PrimeOrder} {m k : ℕ}
    (forms : List (Coefficient p m k)) (st : SimulatorState p m k)
    (hw : WellFormed st) (hl : st.dead=false) (hnodup : forms.Nodup)
    (hnew : ∀ c ∈ forms, c ∉ st.entries.map Prod.fst)
    (hcap : st.entries.length+st.excluded.card+forms.length < 2^labelLength p.val)
    (out : SimulatorState p m k) (hout : out ∈ (allocateForms forms st).support) :
    WellFormed out ∧ out.dead=false ∧ StateExtends st out ∧
      out.entries.map Prod.fst=st.entries.map Prod.fst ++ forms ∧ out.excluded=st.excluded := by
  classical
  induction forms generalizing st out with
  | nil =>
    rw [allocateForms] at hout
    have heq := pure_support_eq_local st out hout
    subst out
    exact ⟨hw,hl,StateExtends_refl st,by simp,rfl⟩
  | cons c cs ih =>
    have hphi : c ∉ cs ∧ cs.Nodup := List.nodup_cons.mp hnodup
    have hc : lookupExpr st c=none := (lookupExpr_none_iff st c).mpr (hnew c List.mem_cons_self)
    have hfresh := freshCodes_nonempty_of_size st (by simp only [List.length_cons] at hcap; omega)
    rw [allocateForms] at hout
    obtain ⟨z,hz,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
    obtain ⟨code,hcode,rfl⟩ := allocate_support_fresh_shape st hl c hc hfresh z hz
    have hnewtail : ∀ d ∈ cs, d ∉
        (({st with entries := st.entries ++ [(c,code)]} : SimulatorState p m k).entries.map Prod.fst) := by
      intro d hd hmem
      simp only [List.map_append,List.map_singleton,List.mem_append,List.mem_singleton] at hmem
      rcases hmem with hmem|heq
      · exact hnew d (List.mem_cons_of_mem c hd) hmem
      · exact hphi.1 (heq ▸ hd)
    have hnextcap :
        ({st with entries := st.entries ++ [(c,code)]} : SimulatorState p m k).entries.length+
          st.excluded.card+cs.length < 2^labelLength p.val := by
      simp only [List.length_append,List.length_singleton]
      simp only [List.length_cons] at hcap
      omega
    have htail := ih _ (WellFormed_append st hw c code hc hcode) hl hphi.2 hnewtail hnextcap out hout
    refine ⟨htail.1,htail.2.1,?_,?_,htail.2.2.2.2⟩
    · have hext : StateExtends st {st with entries := st.entries ++ [(c,code)]} :=
        ⟨⟨[(c,code)],rfl⟩,Finset.Subset.refl _⟩
      exact StateExtends_trans hext htail.2.2.1
    · have hk := htail.2.2.2.1
      simpa only [List.map_append,List.map_singleton,List.append_assoc,List.singleton_append] using hk

lemma initial_state_support {p : PrimeOrder} {m k : ℕ}
    (hcap : m+k+1 < 2^labelLength p.val) (out : SimulatorState p m k)
    (hout : out ∈ (initialSimulatorLaw p m k).support) :
    WellFormed out ∧ out.dead=false ∧ out.entries.map Prod.fst=initialForms p m k ∧
      out.excluded=∅ ∧ InitialAssigned out := by
  classical
  have hbase : WellFormed (emptySimulatorState p m k) := by simp [WellFormed,emptySimulatorState]
  have h := allocateForms_support_keys (initialForms p m k) (emptySimulatorState p m k) hbase rfl
    (initialForms_nodup p m k) (by intro c hc; simp [emptySimulatorState])
    (by simpa only [emptySimulatorState,List.length_nil,Finset.card_empty,zero_add,initialForms_length] using hcap) out hout
  have hk : out.entries.map Prod.fst=initialForms p m k := by simpa [emptySimulatorState] using h.2.2.2.1
  refine ⟨h.1,h.2.1,hk,h.2.2.2.2,?_⟩
  intro c hc
  have hmem : c ∈ out.entries.map Prod.fst := by rw [hk]; exact hc
  obtain ⟨e,he,hec⟩ := List.mem_map.mp hmem
  refine ⟨e.2,?_⟩
  simpa only [← hec,Prod.mk.eta] using he

lemma initial_good_forward {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) :
    (PMF.uniformOfFintype (Encoding p.val)).map
      (fun σ => physicalForms φ σ (initialForms p m k) (emptySimulatorState p m k))=
      initialSimulatorLaw p m k := by
  rw [← physical_empty_uniform φ]
  apply physicalForms_forward_law φ (initialForms p m k) _ (empty_completion_nonempty φ) rfl hphi
  intro c hc e he
  simp [emptySimulatorState] at he


lemma simulatorState_eq {p : PrimeOrder} {m k : ℕ} (st next : SimulatorState p m k)
    (he : st.entries=next.entries) (hf : st.excluded=next.excluded) (hd : st.dead=next.dead) : st=next := by
  cases st
  cases next
  cases he
  cases hf
  cases hd
  rfl

lemma physicalForms_new_eq {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val)
    (forms : List (Coefficient p m k)) (st : SimulatorState p m k) (hnodup : forms.Nodup)
    (hnew : ∀ c ∈ forms, c ∉ st.entries.map Prod.fst) :
    physicalForms φ σ forms st=
      {st with entries := st.entries ++ forms.map (fun c => (c,σ (fieldIndex p (φ c))))} := by
  classical
  induction forms generalizing st with
  | nil => simp [physicalForms]
  | cons c cs ih =>
    have hphi : c ∉ cs ∧ cs.Nodup := List.nodup_cons.mp hnodup
    have hc : lookupExpr st c=none := (lookupExpr_none_iff st c).mpr (hnew c List.mem_cons_self)
    have hnewtail : ∀ d ∈ cs, d ∉
        (({st with entries := st.entries ++ [(c,σ (fieldIndex p (φ c)))]} : SimulatorState p m k).entries.map Prod.fst) := by
      intro d hd hmem
      simp only [List.map_append,List.map_singleton,List.mem_append,List.mem_singleton] at hmem
      rcases hmem with hmem|heq
      · exact hnew d (List.mem_cons_of_mem c hd) hmem
      · exact hphi.1 (heq ▸ hd)
    simp only [physicalForms,physicalAllocate,hc]
    rw [ih _ hphi.2 hnewtail]
    simp only [List.map_cons,List.append_assoc,List.singleton_append]

noncomputable def initialObservedState {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val) : SimulatorState p m k :=
  physicalForms φ σ (initialForms p m k) (emptySimulatorState p m k)

lemma initialObserved_eq_map {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (σ : Encoding p.val) :
    initialObservedState φ σ=
      ⟨(initialForms p m k).map (fun c => (c,σ (fieldIndex p (φ c)))),∅,false⟩ := by
  have h := physicalForms_new_eq φ σ (initialForms p m k) (emptySimulatorState p m k)
    (initialForms_nodup p m k) (by intro c hc; simp [emptySimulatorState])
  simpa only [initialObservedState,emptySimulatorState,List.nil_append] using h

lemma initialObserved_compatible_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (hk : st.entries.map Prod.fst=initialForms p m k) (hf : st.excluded=∅) (hl : st.dead=false)
    (σ : Encoding p.val) : initialObservedState φ σ=st ↔ Compatible φ st σ := by
  constructor
  · intro heq
    rw [← heq]
    exact physicalForms_compatible φ σ _ _ (compatible_empty φ σ)
  · intro hσ
    rw [initialObserved_eq_map]
    apply simulatorState_eq
    · change (initialForms p m k).map (fun c => (c,σ (fieldIndex p (φ c))))=st.entries
      calc
        _ = (st.entries.map Prod.fst).map (fun c => (c,σ (fieldIndex p (φ c)))) := by rw [hk]
        _ = st.entries.map id := by
          rw [List.map_map]
          apply List.map_congr_left
          intro e he
          exact Prod.ext rfl (hσ.1 e he)
        _ = _ := by simp only [List.map_id]
    · exact hf.symm
    · exact hl.symm

noncomputable def initialSigmaKernel {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) : PMF (Encoding p.val) := by
  classical
  exact if h : Nonempty (PhysicalCompletion φ st) then physicalEncodingLaw φ st h else PMF.uniformOfFintype _

lemma initialSigmaKernel_fibre {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (hk : st.entries.map Prod.fst=initialForms p m k) (hf : st.excluded=∅) (hl : st.dead=false) :
    initialSigmaKernel φ st=fibreKernel (initialObservedState φ) st := by
  classical
  let e : {σ : Encoding p.val // initialObservedState φ σ=st} ≃ PhysicalCompletion φ st :=
    { toFun := fun σ => ⟨σ.val,(initialObserved_compatible_iff φ st hk hf hl σ.val).mp σ.property⟩
      invFun := fun σ => ⟨σ.val,(initialObserved_compatible_iff φ st hk hf hl σ.val).mpr σ.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  by_cases hn : Nonempty (PhysicalCompletion φ st)
  · have hobs : Nonempty {σ : Encoding p.val // initialObservedState φ σ=st} := Nonempty.map e.symm hn
    letI := hn
    letI := hobs
    unfold initialSigmaKernel fibreKernel
    rw [dif_pos hn,dif_pos hobs]
    unfold physicalEncodingLaw
    have h := congrArg (fun law : PMF (PhysicalCompletion φ st) => law.map Subtype.val) (uniform_equiv_map e)
    have hv : (Subtype.val ∘ e)=(Subtype.val : {σ : Encoding p.val // initialObservedState φ σ=st} → Encoding p.val) := by
      funext σ
      rfl
    rw [PMF.map_comp,hv] at h
    exact h.symm
  · have hobs : ¬ Nonempty {σ : Encoding p.val // initialObservedState φ σ=st} :=
      fun h => hn (Nonempty.map e h)
    unfold initialSigmaKernel fibreKernel
    rw [dif_neg hn,dif_neg hobs]

lemma Compatible_no_collision {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k)
    (hw : WellFormed st) (σ : Encoding p.val) (hσ : Compatible φ st σ) : ¬ traceCollision φ st := by
  rintro ⟨a,ha,b,hb,hne,heq⟩
  exact hne (congrArg Prod.fst (compatible_entries_injective φ σ st hw hσ a b ha hb heq))

theorem initialSigma_uniform {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (hcap : m+k+1 < 2^labelLength p.val) :
    (initialSimulatorLaw p m k).bind (initialSigmaKernel φ)=PMF.uniformOfFintype (Encoding p.val) := by
  classical
  by_cases hphi : ((initialForms p m k).map φ).Nodup
  · have hlaw : (PMF.uniformOfFintype (Encoding p.val)).map (initialObservedState φ)=initialSimulatorLaw p m k :=
      initial_good_forward φ hphi
    calc
      _ = ((PMF.uniformOfFintype (Encoding p.val)).map (initialObservedState φ)).bind
          (fibreKernel (initialObservedState φ)) := by
        rw [hlaw]
        apply bind_congr_support_local
        intro st hs
        have hst := initial_state_support hcap st hs
        exact initialSigmaKernel_fibre φ st hst.2.2.1 hst.2.2.2.1 hst.2.1
      _ = _ := uniform_fibre_recombine_general (initialObservedState φ)
  · calc
      _ = (initialSimulatorLaw p m k).bind (fun _ => PMF.uniformOfFintype (Encoding p.val)) := by
        apply bind_congr_support_local
        intro st hs
        have hst := initial_state_support hcap st hs
        have hcoll := InitialAssigned_collision φ st hst.2.2.2.2 hphi
        have hempty : ¬ Nonempty (PhysicalCompletion φ st) := by
          rintro ⟨σ,hσ⟩
          exact Compatible_no_collision φ st hst.1 σ hσ hcoll
        simp only [initialSigmaKernel,dif_neg hempty]
      _ = _ := PMF.bind_const _ _

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurityAdversaryCoupling

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

noncomputable def initialJoint {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) : PMF (SimulatorState p m k × Encoding p.val) :=
  (initialSimulatorLaw p m k).bind fun st => (initialSigmaKernel φ st).map (fun σ => (st,σ))

lemma initialJoint_state {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) :
    (initialJoint φ).map Prod.fst=initialSimulatorLaw p m k := by
  unfold initialJoint
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  have hc (st : SimulatorState p m k) : (initialSigmaKernel φ st).map (fun _ => st)=PMF.pure st := PMF.map_const _ _
  simp only [hc]
  exact PMF.bind_pure _

lemma initialJoint_sigma {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (hcap : m+k+1 < 2^labelLength p.val) :
    (initialJoint φ).map Prod.snd=PMF.uniformOfFintype (Encoding p.val) := by
  unfold initialJoint
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  have hc (st : SimulatorState p m k) : (initialSigmaKernel φ st).map (fun σ => σ)=initialSigmaKernel φ st := PMF.map_id _
  simp only [hc]
  exact initialSigma_uniform φ hcap

lemma initialJoint_support_iff {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (z : SimulatorState p m k × Encoding p.val) :
    z ∈ (initialJoint φ).support ↔ z.1 ∈ (initialSimulatorLaw p m k).support ∧ z.2 ∈ (initialSigmaKernel φ z.1).support := by
  unfold initialJoint
  constructor
  · intro hz
    obtain ⟨st,hst,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
    obtain ⟨σ,hσ,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
    exact ⟨hst,hσ⟩
  · rintro ⟨hst,hσ⟩
    apply (PMF.mem_support_bind_iff _ _ z).mpr
    exact ⟨z.1,hst,(PMF.mem_support_map_iff _ _ z).mpr ⟨z.2,hσ,rfl⟩⟩

lemma initial_good_completion_nonempty {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) (st : SimulatorState p m k)
    (hst : st ∈ (initialSimulatorLaw p m k).support) : Nonempty (PhysicalCompletion φ st) := by
  classical
  have hlaw : (PMF.uniformOfFintype (Encoding p.val)).map (initialObservedState φ)=initialSimulatorLaw p m k :=
    initial_good_forward φ hphi
  rw [← hlaw] at hst
  obtain ⟨σ,hσ,heq⟩ := (PMF.mem_support_map_iff _ _ st).mp hst
  refine ⟨⟨σ,?_⟩⟩
  rw [← heq]
  exact physicalForms_compatible φ σ _ _ (compatible_empty φ σ)

lemma initialJoint_good_compatible {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) (z : SimulatorState p m k × Encoding p.val)
    (hz : z ∈ (initialJoint φ).support) : Compatible φ z.1 z.2 := by
  classical
  obtain ⟨hst,hσ⟩ := (initialJoint_support_iff φ z).mp hz
  have hn := initial_good_completion_nonempty φ hphi z.1 hst
  unfold initialSigmaKernel at hσ
  rw [dif_pos hn] at hσ
  exact physicalEncodingLaw_support_compatible φ z.1 hn z.2 hσ

lemma initialJoint_public {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (hcap : m+k+1 < 2^labelLength p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) (hOne : φ (oneCoefficient p m k)=1)
    (z : SimulatorState p m k × Encoding p.val) (hz : z ∈ (initialJoint φ).support) :
    simulatorPublic z.1=physicalPublic φ z.2 := by
  have hs := initial_state_support hcap z.1 ((initialJoint_support_iff φ z).mp hz).1
  exact simulator_public_physical φ z.2 z.1 hs.1 (initialJoint_good_compatible φ hphi z hz) hs.2.2.2.2 hOne

noncomputable def fullSimulatorTrace (p : PrimeOrder) (m k Q : ℕ) (A : Adversary Q) :
    PMF (Bool × SimulatorState p m k) :=
  (initialSimulatorLaw p m k).bind fun st => (A (simulatorPublic st)).bind fun tree => simulatorTree Q tree st

lemma fullSimulatorTrace_output (p : PrimeOrder) (m k Q : ℕ) (A : Adversary Q) :
    (fullSimulatorTrace p m k Q A).map Prod.fst=simulator p m k Q A := by
  simp only [fullSimulatorTrace,simulator,initialSimulatorLaw,emptySimulatorState,PMF.map_bind]

noncomputable def physicalAdversary {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (Q : ℕ) (A : Adversary Q) : PMF Bool :=
  (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
    (A (physicalPublic φ σ)).map fun tree => tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext))


/-- Total proof-side kernel for arbitrary A coin PMFs at a fixed initial state.
The numeric-collision decision is fixed before labels and A coins. -/
noncomputable def adversaryCouplingKernel {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (Q : ℕ) (A : Adversary Q)
    (st : SimulatorState p m k) (σ : Encoding p.val) :
    PMF (Encoding p.val × (Bool × (Bool × SimulatorState p m k))) := by
  classical
  exact if ((initialForms p m k).map φ).Nodup then
      (A (simulatorPublic st)).bind fun tree => (coupledTree φ σ Q tree st).map fun result =>
        (σ,(tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext)),result))
    else
      (A (physicalPublic φ σ)).bind fun realTree =>
        (A (simulatorPublic st)).bind fun simTree => (simulatorTree Q simTree st).map fun result =>
          (σ,(realTree.run (some (⟨p.val,p.property,σ⟩ : GroupContext)),result))

noncomputable def fullCoupledExperiment {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (Q : ℕ) (A : Adversary Q) :
    PMF (Encoding p.val × (Bool × (Bool × SimulatorState p m k))) :=
  (initialJoint φ).bind fun z => adversaryCouplingKernel φ Q A z.1 z.2


lemma initialJoint_bind {p : PrimeOrder} {m k : ℕ} {α : Type*}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)
    (F : SimulatorState p m k × Encoding p.val → PMF α) :
    (initialJoint φ).bind F=(initialSimulatorLaw p m k).bind
      (fun st => (initialSigmaKernel φ st).bind (fun σ => F (st,σ))) := by
  unfold initialJoint
  rw [PMF.bind_bind]
  congr 1
  funext st
  rw [PMF.bind_map]
  rfl

lemma adversaryCouplingKernel_real {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (st : SimulatorState p m k) (σ : Encoding p.val)
    (hpublic : ((initialForms p m k).map φ).Nodup → simulatorPublic st=physicalPublic φ σ) :
    (adversaryCouplingKernel φ Q A st σ).map (fun out => out.2.1)=
      (A (physicalPublic φ σ)).map (fun tree => tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext))) := by
  classical
  by_cases hphi : ((initialForms p m k).map φ).Nodup
  · simp only [adversaryCouplingKernel,if_pos hphi,PMF.map_bind,PMF.map_comp,Function.comp_def]
    have hc (tree : QueryTree Q) :
        (coupledTree φ σ Q tree st).map (fun _ => tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext)))=
          PMF.pure (tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext))) := PMF.map_const _ _
    simp only [hc,hpublic hphi]
    exact PMF.bind_pure_comp _ _
  · simp only [adversaryCouplingKernel,if_neg hphi,PMF.map_bind,PMF.map_comp,Function.comp_def]
    have hc (realTree simTree : QueryTree Q) :
        (simulatorTree Q simTree st).map (fun _ => realTree.run (some (⟨p.val,p.property,σ⟩ : GroupContext)))=
          PMF.pure (realTree.run (some (⟨p.val,p.property,σ⟩ : GroupContext))) := PMF.map_const _ _
    simp only [hc,PMF.bind_const]
    exact PMF.bind_pure_comp _ _

lemma adversaryCouplingKernel_sim_good {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (st : SimulatorState p m k) (σ : Encoding p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) :
    (adversaryCouplingKernel φ Q A st σ).map (fun out => out.2.2)=
      (A (simulatorPublic st)).bind (fun tree => coupledTree φ σ Q tree st) := by
  classical
  simp only [adversaryCouplingKernel,if_pos hphi,PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext tree
  exact PMF.map_id _

lemma adversaryCouplingKernel_sim_bad {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (st : SimulatorState p m k) (σ : Encoding p.val)
    (hphi : ¬ ((initialForms p m k).map φ).Nodup) :
    (adversaryCouplingKernel φ Q A st σ).map (fun out => out.2.2)=
      (A (simulatorPublic st)).bind (fun tree => simulatorTree Q tree st) := by
  classical
  simp only [adversaryCouplingKernel,if_neg hphi,PMF.map_bind,PMF.map_comp,Function.comp_def]
  have hc (tree : QueryTree Q) : (simulatorTree Q tree st).map (fun result => result)=simulatorTree Q tree st := PMF.map_id _
  simp only [hc]
  exact PMF.bind_const _ _

/-- Exact actual-oracle output marginal, with the full public string passed to A. -/
theorem fullCoupledExperiment_real {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) (hOne : φ (oneCoefficient p m k)=1) :
    (fullCoupledExperiment φ Q A).map (fun out => out.2.1)=physicalAdversary φ Q A := by
  classical
  unfold fullCoupledExperiment
  rw [PMF.map_bind]
  calc
    _ = (initialJoint φ).bind (fun z =>
        (A (physicalPublic φ z.2)).map (fun tree => tree.run (some (⟨p.val,p.property,z.2⟩ : GroupContext)))) := by
      apply bind_congr_support_local
      intro z hz
      apply adversaryCouplingKernel_real
      intro hphi
      exact initialJoint_public φ hcap hphi hOne z hz
    _ = ((initialJoint φ).map Prod.snd).bind (fun σ =>
        (A (physicalPublic φ σ)).map (fun tree => tree.run (some (⟨p.val,p.property,σ⟩ : GroupContext)))) := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by rw [initialJoint_sigma φ hcap]; rfl

/-- Exact complete simulated output/state marginal, with no latent coordinate input. -/
theorem fullCoupledExperiment_sim {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) :
    (fullCoupledExperiment φ Q A).map (fun out => out.2.2)=fullSimulatorTrace p m k Q A := by
  classical
  unfold fullCoupledExperiment
  rw [PMF.map_bind,initialJoint_bind]
  unfold fullSimulatorTrace
  apply bind_congr_support_local
  intro st hst
  by_cases hphi : ((initialForms p m k).map φ).Nodup
  · have hn := initial_good_completion_nonempty φ hphi st hst
    simp only [adversaryCouplingKernel_sim_good φ A st _ hphi,initialSigmaKernel,dif_pos hn]
    rw [PMF.bind_comm]
    congr 1
    funext tree
    have hs := initial_state_support hcap st hst
    have hh := coupledTree_right_marginal φ Q tree st hs.1 hn
    rw [coupledTreeLaw_output] at hh
    exact hh
  · simp only [adversaryCouplingKernel_sim_bad φ A st _ hphi]
    exact PMF.bind_const _ _


lemma initial_state_length {p : PrimeOrder} {m k : ℕ}
    (hcap : m+k+1 < 2^labelLength p.val) (st : SimulatorState p m k)
    (hst : st ∈ (initialSimulatorLaw p m k).support) : st.entries.length=m+k+1 := by
  have hk := congrArg List.length (initial_state_support hcap st hst).2.2.1
  simpa only [List.length_map,initialForms_length] using hk

theorem fullSimulatorTrace_length {p : PrimeOrder} {m k Q : ℕ} (A : Adversary Q)
    (hbudget : m+k+1+3*Q < 2^labelLength p.val)
    (out : Bool × SimulatorState p m k) (hout : out ∈ (fullSimulatorTrace p m k Q A).support) :
    out.2.entries.length ≤ m+k+1+Q := by
  classical
  unfold fullSimulatorTrace at hout
  obtain ⟨st,hst,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
  obtain ⟨tree,htree,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hs := initial_state_support hcap st hst
  have hlen := initial_state_length hcap st hst
  have hF : st.excluded.card=0 := by rw [hs.2.2.2.1]; rfl
  have hqcap : st.entries.length+st.excluded.card+3*Q < 2^labelLength p.val := by rw [hlen,hF]; omega
  have hfinal := simulatorTree_support_invariant Q tree st hs.1 hs.2.1 hqcap out hout
  have hfinalLen := hfinal.2.2.2.1
  rw [hlen] at hfinalLen
  exact hfinalLen

lemma fullCoupledExperiment_bad_collision {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (hbudget : m+k+1+3*Q < 2^labelLength p.val)
    (hphi : ¬ ((initialForms p m k).map φ).Nodup)
    (out : Encoding p.val × (Bool × (Bool × SimulatorState p m k)))
    (hout : out ∈ (fullCoupledExperiment φ Q A).support) : traceCollision φ out.2.2.2 := by
  classical
  unfold fullCoupledExperiment at hout
  obtain ⟨z,hz,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
  simp only [adversaryCouplingKernel,if_neg hphi] at hout
  obtain ⟨realTree,hreal,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
  obtain ⟨simTree,hsim,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
  obtain ⟨result,hresult,rfl⟩ := (PMF.mem_support_map_iff _ _ out).mp hout
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hst := ((initialJoint_support_iff φ z).mp hz).1
  have hs := initial_state_support hcap z.1 hst
  have hlen := initial_state_length hcap z.1 hst
  have hF : z.1.excluded.card=0 := by rw [hs.2.2.2.1]; rfl
  have hqcap : z.1.entries.length+z.1.excluded.card+3*Q < 2^labelLength p.val := by rw [hlen,hF]; omega
  have hfinal := simulatorTree_support_invariant Q simTree z.1 hs.1 hs.2.1 hqcap result hresult
  have hcoll := InitialAssigned_collision φ z.1 hs.2.2.2.2 hphi
  exact StateExtends_collision φ hfinal.1 hcoll

/-- Pointwise full-A physical/simulated output agreement off recorded bad events. -/
theorem fullCoupledExperiment_agreement {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (hbudget : m+k+1+3*Q < 2^labelLength p.val)
    (out : Encoding p.val × (Bool × (Bool × SimulatorState p m k)))
    (hout : out ∈ (fullCoupledExperiment φ Q A).support)
    (hnc : ¬ traceCollision φ out.2.2.2) (hng : ¬ traceGuess out.1 out.2.2.2) : out.2.1=out.2.2.1 := by
  classical
  by_cases hphi : ((initialForms p m k).map φ).Nodup
  · unfold fullCoupledExperiment at hout
    obtain ⟨z,hz,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
    simp only [adversaryCouplingKernel,if_pos hphi] at hout
    obtain ⟨tree,htree,hout⟩ := (PMF.mem_support_bind_iff _ _ out).mp hout
    obtain ⟨result,hresult,rfl⟩ := (PMF.mem_support_map_iff _ _ out).mp hout
    have hcap : m+k+1 < 2^labelLength p.val := by omega
    have hst := ((initialJoint_support_iff φ z).mp hz).1
    have hs := initial_state_support hcap z.1 hst
    have hlen := initial_state_length hcap z.1 hst
    have hF : z.1.excluded.card=0 := by rw [hs.2.2.2.1]; rfl
    have hqcap : z.1.entries.length+z.1.excluded.card+3*Q < 2^labelLength p.val := by rw [hlen,hF]; omega
    exact coupledTree_no_bad_agreement φ z.2 Q tree z.1 hs.1 hs.2.1
      (initialJoint_good_compatible φ hphi z hz) hqcap result hresult hnc hng
  · exact False.elim (hnc (fullCoupledExperiment_bad_collision φ A hbudget hphi out hout))


lemma probability_bind_const_bound_general {ι α : Type*}
    (law : PMF ι) (F : ι → PMF α) (E : α → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ i ∈ law.support, probability (F i) E ≤ δ) : probability (law.bind F) E ≤ δ := by
  have hpoint : ∀ i ∈ law.support, (F i).toOuterMeasure {x | E x} ≤ ENNReal.ofReal δ := by
    intro i hi
    calc
      _ = ENNReal.ofReal (((F i).toOuterMeasure {x | E x}).toReal) :=
        (ENNReal.ofReal_toReal (event_outer_finite_local (F i) _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (h i hi)
  have houter : (law.bind F).toOuterMeasure {x | E x} ≤ ENNReal.ofReal δ := by
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' i, law i*ENNReal.ofReal δ := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases hz : law i=0
        · simp only [hz,zero_mul,le_refl]
        · exact mul_le_mul_right (hpoint i hz) (law i)
      _ = _ := by rw [ENNReal.tsum_mul_right,law.tsum_coe,one_mul]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top houter
  simpa only [probability,ENNReal.toReal_ofReal hδ] using hr

lemma probability_mono_support_local {α : Type*} (law : PMF α) (E F : α → Prop)
    (h : ∀ x ∈ law.support, E x → F x) : probability law E ≤ probability law F := by
  classical
  have houter : law.toOuterMeasure {x | E x} ≤ law.toOuterMeasure {x | F x} := by
    rw [PMF.toOuterMeasure_apply,PMF.toOuterMeasure_apply]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hz : law x=0
    · simp only [Set.indicator_apply,Set.mem_ofPred_eq,hz,ite_self,le_refl]
    · by_cases he : E x
      · have hf := h x hz he
        simp only [Set.indicator_apply,Set.mem_ofPred_eq,if_pos he,if_pos hf,le_refl]
      · simp only [Set.indicator_apply,Set.mem_ofPred_eq,if_neg he,zero_le]
  exact ENNReal.toReal_mono (event_outer_finite_local law _) houter

lemma bool_coupling_bound {α : Type*} (law : PMF α) (realBit simBit : α → Bool) (bad : α → Prop)
    (h : ∀ x ∈ law.support, ¬ bad x → realBit x=simBit x) :
    |probability (law.map realBit) (fun b => b=true)-probability (law.map simBit) (fun b => b=true)| ≤
      probability law bad := by
  classical
  rw [probability_map_local,probability_map_local]
  have hRS : probability law (fun x => realBit x=true) ≤ probability law (fun x => simBit x=true)+probability law bad := by
    calc
      _ ≤ probability law (fun x => simBit x=true ∨ bad x) := by
        apply probability_mono_support_local
        intro x hx hr
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ((h x hx hb) ▸ hr)
      _ ≤ _ := probability_or_le_local _ _ _
  have hSR : probability law (fun x => simBit x=true) ≤ probability law (fun x => realBit x=true)+probability law bad := by
    calc
      _ ≤ probability law (fun x => realBit x=true ∨ bad x) := by
        apply probability_mono_support_local
        intro x hx hs
        by_cases hb : bad x
        · exact Or.inr hb
        · exact Or.inl ((h x hx hb).symm ▸ hs)
      _ ≤ _ := probability_or_le_local _ _ _
  apply abs_le.mpr
  constructor <;> linarith


lemma adversaryCouplingKernel_joint_good {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (st : SimulatorState p m k) (σ : Encoding p.val)
    (hphi : ((initialForms p m k).map φ).Nodup) :
    (adversaryCouplingKernel φ Q A st σ).map (fun out => (out.1,out.2.2))=
      (A (simulatorPublic st)).bind (fun tree => (coupledTree φ σ Q tree st).map (fun result => (σ,result))) := by
  classical
  simp only [adversaryCouplingKernel,if_pos hphi,PMF.map_bind,PMF.map_comp,Function.comp_def]

/-- The full arbitrary-A experiment pays at most one conditioned unseen-guess
rate per operand/query, even with infinite-support A coin laws. -/
theorem fullCoupledExperiment_guess_rate {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q) (D : ℕ) (hD : 0 < D)
    (hcapacity : m+k+1+3*Q+D ≤ 2^labelLength p.val) :
    probability (fullCoupledExperiment φ Q A)
      (fun out => guessWithoutCollision φ (out.1,out.2.2)) ≤ (2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  classical
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hbudget : m+k+1+3*Q < 2^labelLength p.val := by omega
  by_cases hphi : ((initialForms p m k).map φ).Nodup
  · have hmap := probability_map_local (fullCoupledExperiment φ Q A) (fun out => (out.1,out.2.2)) (guessWithoutCollision φ)
    rw [← hmap]
    unfold fullCoupledExperiment
    rw [PMF.map_bind,initialJoint_bind]
    apply probability_bind_const_bound_general _ _ _ _ (by positivity)
    intro st hst
    have hn := initial_good_completion_nonempty φ hphi st hst
    simp only [adversaryCouplingKernel_joint_good φ A st _ hphi,initialSigmaKernel,dif_pos hn]
    rw [PMF.bind_comm]
    apply probability_bind_const_bound_general _ _ _ _ (by positivity)
    intro tree htree
    have hs := initial_state_support hcap st hst
    have hlen := initial_state_length hcap st hst
    have hF : st.excluded.card=0 := by rw [hs.2.2.2.1]; rfl
    have hqcap : st.entries.length+st.excluded.card+3*Q+D ≤ 2^labelLength p.val := by rw [hlen,hF]; omega
    exact coupledTree_guess_rate φ D hD Q tree st hs.1 hs.2.1 hn hqcap
  · have hz : probability (fullCoupledExperiment φ Q A)
        (fun out => guessWithoutCollision φ (out.1,out.2.2))=0 := by
      apply probability_eq_zero_of_support_local
      intro out hout hevent
      exact hevent.2 (fullCoupledExperiment_bad_collision φ A hbudget hphi out hout)
    rw [hz]
    positivity


/-- One fixed-evaluation oracle experiment is close to the common explicit
simulator; its only remaining algebraic error is a simulated-form collision. -/
theorem physicalAdversary_simulator_bound {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q) (D : ℕ) (hD : 0 < D)
    (hOne : φ (oneCoefficient p m k)=1)
    (hcapacity : m+k+1+3*Q+D ≤ 2^labelLength p.val) :
    |probability (physicalAdversary φ Q A) (fun b => b=true)-
      probability (simulator p m k Q A) (fun b => b=true)| ≤
      probability (fullSimulatorTrace p m k Q A) (fun result => traceCollision φ result.2)+
        (2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  classical
  let law := fullCoupledExperiment φ Q A
  let bad := fun out : Encoding p.val × (Bool × (Bool × SimulatorState p m k)) =>
    traceCollision φ out.2.2.2 ∨ traceGuess out.1 out.2.2.2
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hbudget : m+k+1+3*Q < 2^labelLength p.val := by omega
  have hbound := bool_coupling_bound law (fun out => out.2.1) (fun out => out.2.2.1) bad (by
    intro out hout hgood
    apply fullCoupledExperiment_agreement φ A hbudget out hout
    · exact fun h => hgood (Or.inl h)
    · exact fun h => hgood (Or.inr h))
  have hreal : law.map (fun out => out.2.1)=physicalAdversary φ Q A :=
    fullCoupledExperiment_real φ A hcap hOne
  have hsim : law.map (fun out => out.2.2.1)=simulator p m k Q A := by
    calc
      _ = (law.map (fun out => out.2.2)).map Prod.fst := by rw [PMF.map_comp]; rfl
      _ = (fullSimulatorTrace p m k Q A).map Prod.fst := by rw [fullCoupledExperiment_sim φ A hcap]
      _ = _ := fullSimulatorTrace_output p m k Q A
  rw [hreal,hsim] at hbound
  have hcoll : probability law (fun out => traceCollision φ out.2.2.2)=
      probability (fullSimulatorTrace p m k Q A) (fun result => traceCollision φ result.2) := by
    have hh := probability_map_local law (fun out => out.2.2) (fun result => traceCollision φ result.2)
    rw [fullCoupledExperiment_sim φ A hcap] at hh
    exact hh.symm
  have hbad : bad=(fun out => traceCollision φ out.2.2.2 ∨
      (traceGuess out.1 out.2.2.2 ∧ ¬ traceCollision φ out.2.2.2)) := by
    funext out
    exact propext (by dsimp only [bad]; tauto)
  calc
    _ ≤ probability law bad := hbound
    _ ≤ probability law (fun out => traceCollision φ out.2.2.2)+
        probability law (fun out => guessWithoutCollision φ (out.1,out.2.2)) := by
      rw [hbad]
      exact probability_or_le_local _ _ _
    _ ≤ _ := by
      rw [hcoll]
      have hh := fullCoupledExperiment_guess_rate φ A D hD hcapacity
      linarith

end GenericGroupWE.Main.GenericSecurityProof

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.CommonMixture

namespace GenericGroupWE.Main

private theorem WitnessEncryption__CommonMixture__pmf_event_finite {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≠ ⊤ := by
  have hu : p.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa using p.tsum_coe
  have hle : p.toOuterMeasure s ≤ 1 := by
    rw [← hu]
    exact p.toOuterMeasure.mono (Set.subset_univ s)
  exact ne_of_lt (hle.trans_lt ENNReal.one_lt_top)

private theorem WitnessEncryption__CommonMixture__common_mixture_one_sided {ι α : Type*} (p : PMF ι)
    (F G : ι → PMF α) (s : Set α) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i ∈ p.support,
      ((F i).toOuterMeasure s).toReal ≤ ((G i).toOuterMeasure s).toReal + ε) :
    ((p.bind F).toOuterMeasure s).toReal ≤
      ((p.bind G).toOuterMeasure s).toReal + ε := by
  have hi : ∀ i ∈ p.support,
      (F i).toOuterMeasure s ≤ (G i).toOuterMeasure s + ENNReal.ofReal ε := by
    intro i his
    calc
      _ = ENNReal.ofReal (((F i).toOuterMeasure s).toReal) :=
        (ENNReal.ofReal_toReal (WitnessEncryption__CommonMixture__pmf_event_finite (F i) s)).symm
      _ ≤ ENNReal.ofReal (((G i).toOuterMeasure s).toReal + ε) :=
        ENNReal.ofReal_le_ofReal (h i his)
      _ = _ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε,
          ENNReal.ofReal_toReal (WitnessEncryption__CommonMixture__pmf_event_finite (G i) s)]
  have hsum : (p.bind F).toOuterMeasure s ≤
      (p.bind G).toOuterMeasure s + ENNReal.ofReal ε := by
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    calc
      ∑' i, p i * (F i).toOuterMeasure s ≤
          ∑' i, p i * ((G i).toOuterMeasure s + ENNReal.ofReal ε) := by
            apply ENNReal.tsum_le_tsum
            intro i
            by_cases hiz : p i = 0
            · simp [hiz]
            · exact mul_le_mul_right (hi i (by simpa [PMF.mem_support_iff] using hiz)) (p i)
      _ = (∑' i, p i * (G i).toOuterMeasure s) + ENNReal.ofReal ε := by
        simp_rw [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
  have hr := ENNReal.toReal_le_add hsum (WitnessEncryption__CommonMixture__pmf_event_finite (p.bind G) s)
    ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal hε] using hr

/-- A common message-independent mixture preserves a componentwise distinguishing bound. -/
theorem common_mixture_bound {ι α : Type*} (p : PMF ι) (F G : ι → PMF α)
    (s : Set α) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i ∈ p.support,
      |((F i).toOuterMeasure s).toReal - ((G i).toOuterMeasure s).toReal| ≤ ε) :
    |((p.bind F).toOuterMeasure s).toReal - ((p.bind G).toOuterMeasure s).toReal| ≤ ε := by
  have hFG := WitnessEncryption__CommonMixture__common_mixture_one_sided p F G s ε hε (by
    intro i hi
    have hab := (abs_le.mp (h i hi)).2
    linarith)
  have hGF := WitnessEncryption__CommonMixture__common_mixture_one_sided p G F s ε hε (by
    intro i hi
    have hab := (abs_le.mp (h i hi)).1
    linarith)
  apply abs_le.mpr
  constructor <;> linarith

end GenericGroupWE.Main

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.ListCollision

namespace GenericGroupWE.Main.ListCollisionProof
open scoped BigOperators ENNReal

def listCollision {α β : Type*} (eval : α → β) (L : List α) : Prop :=
  ∃ a ∈ L, ∃ b ∈ L, a≠b ∧ eval a=eval b

lemma event_finite {ι : Type*} (μ : PMF ι) (event : Set ι) : μ.toOuterMeasure event≠⊤ := by
  have hu : μ.toOuterMeasure Set.univ=1 := by
    rw [PMF.toOuterMeasure_apply]
    simpa using μ.tsum_coe
  have hl : μ.toOuterMeasure event≤1 := by
    rw [←hu]
    exact μ.toOuterMeasure.mono (Set.subset_univ event)
  exact ne_of_lt (hl.trans_lt ENNReal.one_lt_top)

lemma probability_or_le {ι : Type*} (μ : PMF ι) (E F : ι → Prop) :
    probability μ (fun x => E x ∨ F x)≤probability μ E+probability μ F := by
  have hh := MeasureTheory.measure_union_le (μ := μ.toOuterMeasure) {x | E x} {x | F x}
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨event_finite μ _,event_finite μ _⟩) hh
  rw [ENNReal.toReal_add (event_finite μ _) (event_finite μ _)] at hr
  exact hr

theorem probability_finite_union {ι J : Type*} (μ : PMF ι) (s : Finset J) (E : J → ι → Prop) :
    probability μ (fun x => ∃ j ∈ s, E j x)≤∑ j ∈ s, probability μ (E j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probability]
  | @insert j s hj ih =>
    have he : (fun x => ∃ k ∈ insert j s, E k x)=(fun x => E j x ∨ ∃ k ∈ s, E k x) := by
      funext x
      simp
    rw [he,Finset.sum_insert hj]
    have hh := probability_or_le μ (E j) (fun x => ∃ k ∈ s, E k x)
    linarith

theorem fixed_list_collision_bound {ι α β : Type*} (μ : PMF ι) (eval : ι → α → β)
    (ε : ℝ) (hε : 0≤ε)
    (hpair : ∀ a b, a≠b → probability μ (fun ξ => eval ξ a=eval ξ b)≤ε) (L : List α) :
    probability μ (fun ξ => listCollision (eval ξ) L)≤(L.length : ℝ)^2*ε := by
  classical
  let E : (Fin L.length × Fin L.length) → ι → Prop :=
    fun ij ξ => L.get ij.1≠L.get ij.2 ∧ eval ξ (L.get ij.1)=eval ξ (L.get ij.2)
  have he : (fun ξ => listCollision (eval ξ) L)=(fun ξ => ∃ ij ∈ Finset.univ, E ij ξ) := by
    funext ξ
    apply propext
    simp only [listCollision,List.exists_mem_iff_get,Finset.mem_univ,true_and,Prod.exists,E]
  rw [he]
  apply (probability_finite_union μ Finset.univ E).trans
  calc
    (∑ ij ∈ Finset.univ, probability μ (E ij))≤∑ _ij : Fin L.length × Fin L.length, ε := by
      apply Finset.sum_le_sum
      intro ij hij
      by_cases h : L.get ij.1=L.get ij.2
      · have hempty : {ξ | E ij ξ}=(∅ : Set ι) := by
          apply Set.ext
          intro ξ
          change E ij ξ ↔ False
          exact ⟨fun hξ => hξ.1 h,fun hh => False.elim hh⟩
        unfold probability
        rw [hempty]
        simpa using hε
      · have hE : E ij=(fun ξ => eval ξ (L.get ij.1)=eval ξ (L.get ij.2)) := by
          funext ξ
          apply propext
          exact ⟨fun hξ => hξ.2,fun hξ => ⟨h,hξ⟩⟩
        rw [hE]
        exact hpair (L.get ij.1) (L.get ij.2) h
    _ = (L.length : ℝ)^2*ε := by simp [Fintype.card_prod,nsmul_eq_mul,pow_two,Nat.cast_mul]

theorem probability_bind_support_le {ι α : Type*} (μ : PMF ι) (F : ι → PMF α)
    (event : α → Prop) (ε : ℝ) (hε : 0≤ε)
    (h : ∀ i ∈ μ.support, probability (F i) event≤ε) : probability (μ.bind F) event≤ε := by
  have hi : ∀ i ∈ μ.support, (F i).toOuterMeasure {a | event a}≤ENNReal.ofReal ε := by
    intro i his
    calc
      _ = ENNReal.ofReal (probability (F i) event) := (ENNReal.ofReal_toReal (event_finite (F i) _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (h i his)
  have hm : (μ.bind F).toOuterMeasure {a | event a}≤ENNReal.ofReal ε := by
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      (∑' i, μ i*(F i).toOuterMeasure {a | event a})≤∑' i, μ i*ENNReal.ofReal ε := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases hz : μ i=0
        · simp [hz]
        · exact mul_le_mul_right (hi i (by simpa [PMF.mem_support_iff] using hz)) (μ i)
      _ = _ := by rw [ENNReal.tsum_mul_right,μ.tsum_coe,one_mul]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  change ((μ.bind F).toOuterMeasure {a | event a}).toReal≤ε
  simpa only [ENNReal.toReal_ofReal hε] using hr

lemma probability_map {ι α : Type*} (μ : PMF ι) (f : ι → α) (event : α → Prop) :
    probability (μ.map f) event=probability μ (fun x => event (f x)) := by
  unfold probability
  rw [PMF.toOuterMeasure_map_apply]
  rfl

theorem independent_list_collision_bound {ι α β : Type*} (μ : PMF ι) (τ : PMF (List α))
    (eval : ι → α → β) (ε : ℝ) (hε : 0≤ε)
    (hpair : ∀ a b, a≠b → probability μ (fun ξ => eval ξ a=eval ξ b)≤ε)
    (H : ℕ) (hH : ∀ L ∈ τ.support, L.length≤H) :
    probability (τ.bind (fun L => μ.map (fun ξ => (ξ,L))))
      (fun z => listCollision (eval z.1) z.2)≤(H : ℝ)^2*ε := by
  apply probability_bind_support_le τ _ _ _ (by positivity)
  intro L hL
  rw [probability_map]
  apply (fixed_list_collision_bound μ eval ε hε hpair L).trans
  apply mul_le_mul_of_nonneg_right _ hε
  have hh : (L.length : ℝ)≤(H : ℝ) := by exact_mod_cast hH L hL
  have h0 : (0 : ℝ)≤L.length := by positivity
  have h1 : (0 : ℝ)≤H := by positivity
  nlinarith

end GenericGroupWE.Main.ListCollisionProof


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.UniformAffineTest

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

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.ShortAffineFiber

namespace GenericGroupWE.Main
open scoped BigOperators

namespace FixedTestProof
open Module

lemma pivot_columns {K : Type*} [Field K] (m : ℕ) (A : Matrix (Fin m) (Fin m) K) :
    ∃ c : Fin A.rank → Fin m, Function.Injective c ∧
      LinearIndependent K (fun j => fun i => A i (c j)) := by
  classical
  rw [A.rank_eq_finrank_span_cols]
  obtain ⟨f, hfmem, _, hfLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  choose c hc using hfmem
  have hLI : LinearIndependent K (fun j => fun i => A i (c j)) := by
    have heq : (fun j => fun i => A i (c j)) = f := by
      funext j
      exact hc j
    exact heq.symm ▸ hfLI
  exact ⟨c, fun i j h => hLI.injective (by simp only [h]), hLI⟩

lemma fiber_card_bound {K : Type*} [Field K] (m : ℕ) (A : Matrix (Fin m) (Fin m) K)
    (short : Fin m → K) (hshort : Function.Injective short) (b : Fin m → K) :
    Nat.card {r : Fin m → Fin m | A.mulVec (fun i => short (r i)) = b} ≤ m^(m-A.rank) := by
  classical
  obtain ⟨c, hc, hLI⟩ := pivot_columns m A
  let S : Finset (Fin m) := Finset.univ.image c
  let T := {i : Fin m // i ∉ S}
  let E : Set (Fin m → Fin m) := {r | A.mulVec (fun i => short (r i)) = b}
  let restrict : E → (T → Fin m) := fun r i => r.val i.val
  have hinj : Function.Injective restrict := by
    intro r s hrs
    let v : Fin m → K := fun i => short (r.val i)-short (s.val i)
    have hv0 : A.mulVec v = 0 := by
      change A.mulVec ((fun i => short (r.val i)) - (fun i => short (s.val i))) = 0
      rw [Matrix.mulVec_sub, r.property, s.property, sub_self]
    have hvout : ∀ i : Fin m, i ∉ S → v i = 0 := by
      intro i hi
      have heq := congrFun hrs (⟨i,hi⟩ : T)
      change r.val i = s.val i at heq
      dsimp [v]
      rw [heq, sub_self]
    have hsupport : (∑ i : Fin m, v i • (fun row => A row i)) =
        ∑ j : Fin A.rank, v (c j) • (fun row => A row (c j)) := by
      calc
        _ = ∑ i ∈ S, v i • (fun row => A row i) := by
          apply (Finset.sum_subset (Finset.subset_univ S) ?_).symm
          intro i _ hi
          rw [hvout i hi, zero_smul]
        _ = _ := by
          dsimp [S]
          rw [Finset.sum_image (fun i _ j _ h => hc h)]
    have hsum : (∑ j : Fin A.rank, v (c j) • (fun row => A row (c j))) = 0 := by
      rw [← hsupport]
      have hmat : A.mulVec v = ∑ i : Fin m, v i • (fun row => A row i) := by
        ext row
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      rw [← hmat, hv0]
    have hpivot : ∀ j, v (c j) = 0 := (Fintype.linearIndependent_iff.mp hLI) _ hsum
    apply Subtype.ext
    funext i
    apply hshort
    apply sub_eq_zero.mp
    change v i = 0
    by_cases hi : i ∈ S
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
      simpa only [hj] using hpivot j
    · exact hvout i hi
  have hcardS : S.card = A.rank := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hc, Finset.card_univ, Fintype.card_fin]
  have hcardT : Fintype.card T = m-A.rank := by
    have h := Fintype.card_subtype_compl (fun i : Fin m => i ∈ S)
    simpa only [Fintype.card_fin, Fintype.card_coe, hcardS] using h
  have hcount := Nat.card_le_card_of_injective restrict hinj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hcardT] using hcount

end FixedTestProof

theorem short_affine_fiber_bound :
    ∀ (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (hp : m ≤ p.val)
      (A : Matrix (Fin m) (Fin m) (ZMod p.val)) (b : Fin m → ZMod p.val),
      letI : NeZero m := ⟨hm.ne'⟩
      probability (PMF.uniformOfFintype (Fin m → Fin m))
        (fun r => A.mulVec (fun i => ((r i).val+1 : ℕ)) = b) ≤
          (m : ℝ)^(-(A.rank : ℝ)) := by
  intro m hm p hp A b
  letI : NeZero m := ⟨hm.ne'⟩
  have hcard := FixedTestProof.fiber_card_bound m A (fun r => ((r.val+1 : ℕ) : ZMod p.val))
    (FixedTestProof.short_cast_injective m p hp) b
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [FixedTestProof.uniform_probability]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (Nat.card {r : Fin m → Fin m | A.mulVec (fun i => ((r i).val+1 : ℕ)) = b} : ℝ) /
        (m : ℝ)^m ≤ (m : ℝ)^(m-A.rank)/(m : ℝ)^m := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ = (m : ℝ)^(-(A.rank : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub hm0,
        Nat.cast_sub A.rank_le_width]
      congr 1
      ring

end GenericGroupWE.Main

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.FixedTests
namespace GenericGroupWE.Main
open scoped BigOperators
namespace FixedTestProof

lemma zero_test_algebra (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β s : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val)
    (r : Fin m → Fin m) :
    α + (∑ i, β i*s i) + (∑ j, γ j * ∑ i : Fin m, ∑ l : Fin m,
      s i * B.matrices j i l * ((r l).val+1 : ℕ)) =
    α + ∑ i, (β i + (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i)*s i := by
  classical
  simp only [MatrixBundle.combination, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [← add_assoc]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma affine_pair_bound (m k : ℕ) (p : PrimeOrder)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin k → ZMod p.val)
    (hne : ¬ (α = 0 ∧ β = 0 ∧ γ = 0)) :
    probability (PMF.uniformOfFintype ((Fin m → ZMod p.val) × (Fin k → ZMod p.val)))
      (fun z => α + (∑ i, β i*z.1 i) + (∑ j, γ j*z.2 j) = 0) ≤ (p.val : ℝ)⁻¹ := by
  classical
  let e := Equiv.sumArrowEquivProdArrow (Fin m) (Fin k) (ZMod p.val)
  have hn : ¬ (α = 0 ∧ Sum.elim β γ = 0) := by
    rintro ⟨hα,hc⟩
    apply hne
    refine ⟨hα, ?_, ?_⟩
    · funext i
      exact congrFun hc (Sum.inl i)
    · funext j
      exact congrFun hc (Sum.inr j)
  rw [← uniform_probability_equiv e]
  simpa only [e, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.sumArrowEquivProdArrow_apply_snd, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    add_assoc] using uniform_affine_test_bound p (Fin m ⊕ Fin k) α (Sum.elim β γ) hn

def rearrange_true {S R T : Type*} : (S × R × T) ≃ (S × T) × R where
  toFun x := ((x.1,x.2.2),x.2.1)
  invFun x := (x.1.1,x.2,x.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def rearrange_false {S R T : Type*} : (S × R × T) ≃ (R × S) × T where
  toFun x := ((x.2.1,x.1),x.2.2)
  invFun x := (x.1.2,x.1.1,x.2)
  left_inv _ := rfl
  right_inv _ := rfl

lemma true_test_bound (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val)
    (hne : ¬ (α = 0 ∧ β = 0 ∧ γ = 0)) :
    fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹ := by
  letI : NeZero m := ⟨hm.ne'⟩
  let event : ((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val)) → Prop :=
    fun z => α + (∑ i, β i*z.1 i) + (∑ j, γ j*z.2 j) = 0
  have heq := uniform_probability_equiv
    (rearrange_true (S := Fin m → ZMod p.val) (R := Fin m → Fin m) (T := Fin B.k → ZMod p.val))
    (fun z => event z.1)
  calc
    fixedTestProbability B hm α β γ true =
        probability (PMF.uniformOfFintype
          (((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val)) × (Fin m → Fin m)))
          (fun z => event z.1) := by
      simpa only [fixedTestProbability, exactCoordinates, event, rearrange_true,
        Equiv.coe_fn_mk, ite_true] using heq
    _ = probability (PMF.uniformOfFintype
        ((Fin m → ZMod p.val) × (Fin B.k → ZMod p.val))) event := uniform_ignore_right event
    _ ≤ _ := affine_pair_bound m B.k p α β γ hne

lemma false_test_probability (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val) :
    letI : NeZero m := ⟨hm.ne'⟩
    fixedTestProbability B hm α β γ false =
      probability (PMF.uniformOfFintype ((Fin m → Fin m) × (Fin m → ZMod p.val)))
        (fun z => α + ∑ i, (β i + (B.combination γ).mulVec
          (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0) := by
  letI : NeZero m := ⟨hm.ne'⟩
  let event : ((Fin m → Fin m) × (Fin m → ZMod p.val)) → Prop :=
    fun z => α + ∑ i, (β i + (B.combination γ).mulVec
      (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0
  have heq := uniform_probability_equiv
    (rearrange_false (S := Fin m → ZMod p.val) (R := Fin m → Fin m) (T := Fin B.k → ZMod p.val))
    (fun z => event z.1)
  calc
    fixedTestProbability B hm α β γ false =
        probability (PMF.uniformOfFintype
          (((Fin m → Fin m) × (Fin m → ZMod p.val)) × (Fin B.k → ZMod p.val)))
          (fun z => event z.1) := by
      convert heq using 1
      unfold fixedTestProbability exactCoordinates
      congr 1
      funext z
      simp only [Bool.false_eq_true, ↓reduceIte, rearrange_false, Equiv.coe_fn_mk, event]
      exact congrArg (fun x : ZMod p.val => x = 0) (zero_test_algebra m p B α β z.1 γ z.2.1)
    _ = _ := uniform_ignore_right event


end FixedTestProof
end GenericGroupWE.Main



namespace GenericGroupWE.Main
open scoped BigOperators

theorem lemma_3_4 (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (B : MatrixBundle m p)
    (hp : m ≤ p.val)
    (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 →
      R ≤ (B.combination a).rank)
    (α : ZMod p.val) (β : Fin m → ZMod p.val) (γ : Fin B.k → ZMod p.val) :
    ((α = 0 ∧ β = 0 ∧ γ = 0) → ∀ message,
      fixedTestProbability B hm α β γ message = 1) ∧
    ((¬ (α = 0 ∧ β = 0 ∧ γ = 0)) →
      (∀ message, fixedTestProbability B hm α β γ message ≤
        (m : ℝ)^(-R) + (p.val : ℝ)⁻¹) ∧
      fixedTestProbability B hm α β γ true ≤ (p.val : ℝ)⁻¹) := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  constructor
  · rintro ⟨rfl,rfl,rfl⟩ message
    exact FixedTestProof.trivial_test m hm p B message
  · intro hne
    have htrue := FixedTestProof.true_test_bound m hm p B α β γ hne
    refine ⟨?_, htrue⟩
    intro message
    have hpow : 0 ≤ (m : ℝ)^(-R) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    cases message with
    | true => exact htrue.trans (by linarith)
    | false =>
      rw [FixedTestProof.false_test_probability]
      let event : ((Fin m → Fin m) × (Fin m → ZMod p.val)) → Prop :=
        fun z => α + ∑ i, (β i + (B.combination γ).mulVec
          (fun l => ((z.1 l).val+1 : ℕ)) i)*z.2 i = 0
      change probability (PMF.uniformOfFintype _) event ≤ _
      by_cases hγ : γ = 0
      · have hαβ : ¬ (α = 0 ∧ β = 0) := fun h => hne ⟨h.1,h.2,hγ⟩
        have hA : B.combination γ = 0 := by simp [MatrixBundle.combination, hγ]
        have hb := FixedTestProof.uniform_condition_bound event (fun _ => False) (p.val : ℝ)⁻¹
          (by positivity) (by
            intro r _
            simpa only [event, hA, Matrix.zero_mulVec, Pi.zero_apply, add_zero] using
              uniform_affine_test_bound p (Fin m) α β hαβ)
        simp only [FixedTestProof.uniform_probability_const, if_false, zero_add] at hb
        exact hb.trans (by linarith)
      · have hA : B.combination γ ≠ 0 := by
          intro hz
          apply hγ
          funext j
          exact (Fintype.linearIndependent_iff.mp hlin) γ
            (by simpa only [MatrixBundle.combination] using hz) j
        let bad : (Fin m → Fin m) → Prop :=
          fun r => (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) = -β
        have hb := FixedTestProof.uniform_condition_bound event bad (p.val : ℝ)⁻¹
          (by positivity) (by
            intro r hr
            apply uniform_affine_test_bound p (Fin m) α
              (fun i => β i+(B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i)
            rintro ⟨_,hcoeff⟩
            apply hr
            funext i
            have hi := congrFun hcoeff i
            change β i + (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i = 0 at hi
            change (B.combination γ).mulVec (fun l => ((r l).val+1 : ℕ)) i = -β i
            linear_combination hi)
        have hfiber := short_affine_fiber_bound m hm p hp (B.combination γ) (-β)
        have hR := hrank γ hA
        have hM1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
        have hexp : (m : ℝ)^(-((B.combination γ).rank : ℝ)) ≤ (m : ℝ)^(-R) :=
          Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
        exact hb.trans (add_le_add (hfiber.trans hexp) (le_refl _))

end GenericGroupWE.Main



-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.BoundedUniform

open scoped BigOperators ENNReal

namespace GenericGroupWE.Main

private theorem WitnessEncryption__BoundedUniform__bounded_uniform_step (D a : ℕ) (hD : 0 < D) (y : Option ℕ) :
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

private theorem WitnessEncryption__BoundedUniform__bounded_uniform_failure_step (D a : ℕ) (hD : 0 < D) :
    boundedUniform D (a+1) none =
      ((2 ^ Nat.clog 2 D - D : ℕ) : ℝ≥0∞) *
        (((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * boundedUniform D a none) := by
  rw [WitnessEncryption__BoundedUniform__bounded_uniform_step D a hD]
  simp

private theorem WitnessEncryption__BoundedUniform__bounded_uniform_success_step (D a x : ℕ) (hD : 0 < D) :
    boundedUniform D (a+1) (some x) =
      (if x < D then ((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ else 0) +
      ((2 ^ Nat.clog 2 D - D : ℕ) : ℝ≥0∞) *
        (((2 ^ Nat.clog 2 D : ℕ) : ℝ≥0∞)⁻¹ * boundedUniform D a (some x)) := by
  classical
  rw [WitnessEncryption__BoundedUniform__bounded_uniform_step D a hD]
  simp [PMF.pure_apply, mul_ite]

private theorem WitnessEncryption__BoundedUniform__bounded_uniform_real_law (D : ℕ) (hD : 0 < D) :
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
    rw [WitnessEncryption__BoundedUniform__bounded_uniform_failure_step D a hD]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    dsimp [q, M]
    ring
  have hs (a x : ℕ) : (boundedUniform D (a+1) (some x)).toReal =
      (if x < D then (M : ℝ)⁻¹ else 0) +
        q * (boundedUniform D a (some x)).toReal := by
    have hn := (boundedUniform D (a+1)).apply_ne_top (some x)
    rw [WitnessEncryption__BoundedUniform__bounded_uniform_success_step D a x hD] at hn ⊢
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
  obtain ⟨hf, hs⟩ := WitnessEncryption__BoundedUniform__bounded_uniform_real_law D hD a
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


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.BoundedCoordinates

open scoped ENNReal BigOperators
namespace GenericGroupWE.Main

private def WitnessEncryption__BoundedCoordinates__optionCons (a : Option ℕ) (xs : Option (List ℕ)) : Option (List ℕ) := do
  let a ← a
  let xs ← xs
  pure (a :: xs)

private theorem WitnessEncryption__BoundedCoordinates__optionCons_none (a : Option ℕ) (xs : Option (List ℕ)) :
    none = WitnessEncryption__BoundedCoordinates__optionCons a xs ↔ a = none ∨ xs = none := by
  cases a <;> cases xs <;> simp [WitnessEncryption__BoundedCoordinates__optionCons]

private theorem WitnessEncryption__BoundedCoordinates__optionCons_some (a : Option ℕ) (ys : Option (List ℕ)) (x : ℕ) (xs : List ℕ) :
    some (x :: xs) = WitnessEncryption__BoundedCoordinates__optionCons a ys ↔ a = some x ∧ ys = some xs := by
  cases a <;> cases ys <;> simp [WitnessEncryption__BoundedCoordinates__optionCons, eq_comm, and_comm]

private theorem WitnessEncryption__BoundedCoordinates__optionCons_empty (a : Option ℕ) (xs : Option (List ℕ)) :
    some [] ≠ WitnessEncryption__BoundedCoordinates__optionCons a xs := by
  cases a <;> cases xs <;> simp [WitnessEncryption__BoundedCoordinates__optionCons]

private theorem WitnessEncryption__BoundedCoordinates__option_tsum_split {α : Type*} (f : Option α → ENNReal) :
    (∑' x, f x) = f none + ∑' x, if x = none then 0 else f x := by
  classical
  refine (ENNReal.tsum_eq_add_tsum_ite (f := f) none).trans ?_
  congr 1
  apply tsum_congr
  intro x
  by_cases hx : x = none <;> simp [hx]

private theorem WitnessEncryption__BoundedCoordinates__option_pmf_complement {α : Type*} (p : PMF (Option α)) :
    (∑' x, if x = none then 0 else p x) = 1 - p none := by
  classical
  have h := ENNReal.tsum_eq_add_tsum_ite (f := fun x => p x) none
  rw [p.tsum_coe] at h
  convert (ENNReal.sub_eq_of_eq_add_rev (p.apply_ne_top none) h).symm using 1
  apply tsum_congr
  intro x
  by_cases hx : x = none <;> simp [hx]

private theorem WitnessEncryption__BoundedCoordinates__bounded_coordinates_failure_step (a D : ℕ) (Ds : List ℕ) :
    boundedCoordinates a (D :: Ds) none = boundedUniform D a none +
      (1 - boundedUniform D a none) * boundedCoordinates a Ds none := by
  classical
  let p := boundedUniform D a
  let q := boundedCoordinates a Ds
  change (p.bind fun x => q.map (WitnessEncryption__BoundedCoordinates__optionCons x)) none = p none + (1 - p none) * q none
  rw [PMF.bind_apply]
  have inner (x : Option ℕ) : (q.map (WitnessEncryption__BoundedCoordinates__optionCons x)) none =
      if x = none then 1 else q none := by
    rw [PMF.map_apply]
    simp only [WitnessEncryption__BoundedCoordinates__optionCons_none]
    by_cases hx : x = none <;> simp [hx, q.tsum_coe]
  simp_rw [inner]
  rw [WitnessEncryption__BoundedCoordinates__option_tsum_split]
  simp only [↓reduceIte, mul_one]
  congr 1
  calc
    (∑' x, if x = none then 0 else p x * (if x = none then 1 else q none)) =
        ∑' x, (if x = none then 0 else p x) * q none := by
      apply tsum_congr
      intro x
      by_cases hx : x = none <;> simp [hx]
    _ = (∑' x, if x = none then 0 else p x) * q none := ENNReal.tsum_mul_right
    _ = (1 - p none) * q none := by rw [WitnessEncryption__BoundedCoordinates__option_pmf_complement]

private theorem WitnessEncryption__BoundedCoordinates__bounded_coordinates_success_step (a D x : ℕ) (Ds xs : List ℕ) :
    boundedCoordinates a (D :: Ds) (some (x :: xs)) =
      boundedUniform D a (some x) * boundedCoordinates a Ds (some xs) := by
  classical
  let p := boundedUniform D a
  let q := boundedCoordinates a Ds
  change (p.bind fun y => q.map (WitnessEncryption__BoundedCoordinates__optionCons y)) (some (x :: xs)) = p (some x) * q (some xs)
  rw [PMF.bind_apply]
  simp_rw [PMF.map_apply, WitnessEncryption__BoundedCoordinates__optionCons_some, ite_and]
  have inner (y : Option ℕ) :
      (∑' ys, if y = some x then if ys = some xs then q ys else 0 else 0) =
        if y = some x then q (some xs) else 0 := by
    by_cases hy : y = some x <;> simp [hy]
  simp_rw [inner, mul_ite, mul_zero]
  simp

private theorem WitnessEncryption__BoundedCoordinates__bounded_coordinates_empty_step (a D : ℕ) (Ds : List ℕ) :
    boundedCoordinates a (D :: Ds) (some []) = 0 := by
  classical
  change ((boundedUniform D a).bind fun y =>
    (boundedCoordinates a Ds).map (WitnessEncryption__BoundedCoordinates__optionCons y)) (some []) = 0
  simp only [PMF.bind_apply, PMF.map_apply, WitnessEncryption__BoundedCoordinates__optionCons_empty, if_false, tsum_zero, mul_zero]

private theorem WitnessEncryption__BoundedCoordinates__bounded_uniform_normalized (D a : ℕ) (hD : 0 < D) (x : ℕ) :
    boundedUniform D a (some x) = (1 - boundedUniform D a none) *
      (if x < D then (D : ENNReal)⁻¹ else 0) := by
  have hzero : (D : ENNReal) ≠ 0 := by exact_mod_cast hD.ne'
  have h := congrArg (fun z : ENNReal => z * (D : ENNReal)⁻¹)
    ((bounded_uniform_law D a hD).2 x)
  rw [ENNReal.mul_inv_cancel_right hzero (by simp)] at h
  by_cases hx : x < D <;> simpa [hx] using h

private theorem WitnessEncryption__BoundedCoordinates__bounded_coordinates_success_mass (a D : ℕ) (Ds : List ℕ) :
    1 - boundedCoordinates a (D :: Ds) none =
      (1 - boundedUniform D a none) * (1 - boundedCoordinates a Ds none) := by
  rw [WitnessEncryption__BoundedCoordinates__bounded_coordinates_failure_step]
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
          WitnessEncryption__BoundedCoordinates__bounded_coordinates_failure_step a D Ds
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
      | nil => rw [WitnessEncryption__BoundedCoordinates__bounded_coordinates_empty_step]; simp
      | cons x xs =>
        rw [WitnessEncryption__BoundedCoordinates__bounded_coordinates_success_step, WitnessEncryption__BoundedCoordinates__bounded_uniform_normalized D a hD,
          hpoints xs, WitnessEncryption__BoundedCoordinates__bounded_coordinates_success_mass]
        by_cases hx : x < D <;>
          by_cases hxs : List.Forall₂ (fun x D : ℕ => x < D) xs Ds <;>
          simp [hx, hxs, List.forall₂_cons] <;> ac_rfl

end GenericGroupWE.Main


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.CoordinateListCodec

namespace GenericGroupWE.Main

private abbrev WitnessEncryption__CoordinateListCodec__CoordinateTriple (m k : ℕ) (p : PrimeOrder) :=
  (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin k → ZMod p.val)

private def WitnessEncryption__CoordinateListCodec__coordinateList {m k : ℕ} {p : PrimeOrder} (z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p) : List ℕ :=
  List.ofFn (fun i => (z.1 i).val) ++ List.ofFn (fun i => (z.2.1 i).val) ++
    List.ofFn (fun i => (z.2.2 i).val)

private theorem WitnessEncryption__CoordinateListCodec__getD_ofFn {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem (List.ofFn f) d (by simpa using i.isLt), List.getElem_ofFn]

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_first {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p) (i : Fin m) :
    ((WitnessEncryption__CoordinateListCodec__coordinateList z).getD i.val 0 : ZMod p.val) = z.1 i := by
  dsimp [WitnessEncryption__CoordinateListCodec__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append _ _ _ _ (by simpa using i.isLt), WitnessEncryption__CoordinateListCodec__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_middle {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p) (i : Fin m) :
    (WitnessEncryption__CoordinateListCodec__coordinateList z).getD (m+i.val) 0 = (z.2.1 i).val := by
  dsimp [WitnessEncryption__CoordinateListCodec__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  exact WitnessEncryption__CoordinateListCodec__getD_ofFn _ i _

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_last {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p) (i : Fin k) :
    ((WitnessEncryption__CoordinateListCodec__coordinateList z).getD (2*m+i.val) 0 : ZMod p.val) = z.2.2 i := by
  dsimp [WitnessEncryption__CoordinateListCodec__coordinateList]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 2*m+i.val-(m+m) = i.val by omega, WitnessEncryption__CoordinateListCodec__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_injective (m k : ℕ) (p : PrimeOrder) :
    Function.Injective (WitnessEncryption__CoordinateListCodec__coordinateList (m := m) (k := k) (p := p)) := by
  intro z w h
  apply Prod.ext
  · funext i
    have hi := congrArg (fun xs : List ℕ => (xs.getD i.val 0 : ZMod p.val)) h
    simpa only [WitnessEncryption__CoordinateListCodec__coordinate_list_first] using hi
  · apply Prod.ext
    · funext i
      apply Fin.ext
      have hi := congrArg (fun xs : List ℕ => xs.getD (m+i.val) 0) h
      simpa only [WitnessEncryption__CoordinateListCodec__coordinate_list_middle] using hi
    · funext i
      have hi := congrArg (fun xs : List ℕ => (xs.getD (2*m+i.val) 0 : ZMod p.val)) h
      simpa only [WitnessEncryption__CoordinateListCodec__coordinate_list_last] using hi

private theorem WitnessEncryption__CoordinateListCodec__ofFn_lt_replicate (N D : ℕ) (f : Fin N → ℕ) (hf : ∀ i, f i < D) :
    List.Forall₂ (fun x d : ℕ => x < d) (List.ofFn f) (List.replicate N D) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi1 hi2
  have hi : i < N := by simpa using hi1
  rw [← List.getD_eq_get (List.ofFn f) 0 ⟨i,hi1⟩,
    ← List.getD_eq_get (List.replicate N D) 0 ⟨i,hi2⟩,
    WitnessEncryption__CoordinateListCodec__getD_ofFn f ⟨i,hi⟩ 0, List.getD_replicate D hi]
  exact hf _

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_valid {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p) :
    List.Forall₂ (fun x D : ℕ => x < D) (WitnessEncryption__CoordinateListCodec__coordinateList z) (coordinateBounds m k p.val) := by
  exact List.rel_append
    (List.rel_append (WitnessEncryption__CoordinateListCodec__ofFn_lt_replicate m p.val _ (fun i => ZMod.val_lt _))
      (WitnessEncryption__CoordinateListCodec__ofFn_lt_replicate m m _ (fun i => (z.2.1 i).isLt)))
    (WitnessEncryption__CoordinateListCodec__ofFn_lt_replicate k p.val _ (fun i => ZMod.val_lt _))

private theorem WitnessEncryption__CoordinateListCodec__vector_of_bounded_list (N D : ℕ) (xs : List ℕ)
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

private theorem WitnessEncryption__CoordinateListCodec__coordinate_list_surjective (m k : ℕ) (p : PrimeOrder) (xs : List ℕ)
    (h : List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m k p.val)) :
    ∃ z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p, WitnessEncryption__CoordinateListCodec__coordinateList z = xs := by
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
  obtain ⟨s,hs⟩ := WitnessEncryption__CoordinateListCodec__vector_of_bounded_list m p.val (xs.take m) hs
  obtain ⟨r,hr⟩ := WitnessEncryption__CoordinateListCodec__vector_of_bounded_list m m ((xs.drop m).take m) hr
  obtain ⟨t,ht⟩ := WitnessEncryption__CoordinateListCodec__vector_of_bounded_list k p.val ((xs.drop m).drop m) ht
  let z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p :=
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
  change Function.Injective (WitnessEncryption__CoordinateListCodec__coordinateList (m := m) (k := k) (p := p)) ∧
    ∀ xs : List ℕ, (∃ z : WitnessEncryption__CoordinateListCodec__CoordinateTriple m k p, WitnessEncryption__CoordinateListCodec__coordinateList z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m k p.val)
  refine ⟨WitnessEncryption__CoordinateListCodec__coordinate_list_injective m k p, ?_⟩
  intro xs
  constructor
  · rintro ⟨z,rfl⟩
    exact WitnessEncryption__CoordinateListCodec__coordinate_list_valid z
  · exact WitnessEncryption__CoordinateListCodec__coordinate_list_surjective m k p xs


end GenericGroupWE.Main


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.SamplingDistribution

open scoped ENNReal BigOperators
namespace GenericGroupWE.Main

private theorem WitnessEncryption__SamplingDistribution__coordinate_bounds_positive (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (k : ℕ) :
    ∀ D ∈ coordinateBounds m k p.val, 0 < D := by
  intro D hD
  have hp := p.property.pos
  simp only [coordinateBounds, List.mem_append, List.mem_replicate] at hD
  omega

private theorem WitnessEncryption__SamplingDistribution__coordinate_bounds_length (m k p : ℕ) :
    (coordinateBounds m k p).length = 2*m+k := by
  simp [coordinateBounds]
  omega

private theorem WitnessEncryption__SamplingDistribution__sampling_failure_bound (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (n : ℕ) :
    samplingFailure B n ≤ (2 : ℝ)^(-(n : ℝ)-2) := by
  have hv := (bounded_coordinates_law (coordinateAttempts n m B.k)
    (coordinateBounds m B.k p.val) (WitnessEncryption__SamplingDistribution__coordinate_bounds_positive m hm p B.k)).1
  have hreal := ENNReal.toReal_mono (by finiteness) hv
  simp only [WitnessEncryption__SamplingDistribution__coordinate_bounds_length, ENNReal.toReal_mul, ENNReal.toReal_natCast,
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

private theorem WitnessEncryption__SamplingDistribution__option_tsum (α : Type*) (f : Option α → ENNReal) :
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

private theorem WitnessEncryption__SamplingDistribution__coordinate_ciphertext_not_abort (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (σ : Encoding p.val) (s : Fin m → ZMod p.val) (r : Fin m → ℕ)
    (t : Fin B.k → ZMod p.val) (message : Bool) :
    abortCiphertext ≠ coordinateCiphertext B σ s r t message := by
  intro h
  have houtput := congrArg Ciphertext.output h
  simp [abortCiphertext, coordinateCiphertext] at houtput

private theorem WitnessEncryption__SamplingDistribution__sampling_abort_mass (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (n : ℕ) (message : Bool) :
    (boundedEncryption B n message) abortCiphertext = (samplingLaw B n) none := by
  classical
  rw [boundedEncryption, PMF.bind_apply, WitnessEncryption__SamplingDistribution__option_tsum]
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
    exact if_neg (WitnessEncryption__SamplingDistribution__coordinate_ciphertext_not_abort m p B σ _ _ _ message)
  rw [hzero, mul_zero]

private abbrev WitnessEncryption__SamplingDistribution__CoordinateTriple (m k : ℕ) (p : PrimeOrder) :=
  (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin k → ZMod p.val)

private def WitnessEncryption__SamplingDistribution__coordinateList {m k : ℕ} {p : PrimeOrder} (z : WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) : List ℕ :=
  List.ofFn (fun i => (z.1 i).val) ++ List.ofFn (fun i => (z.2.1 i).val) ++
    List.ofFn (fun i => (z.2.2 i).val)

private theorem WitnessEncryption__SamplingDistribution__getD_ofFn {α : Type*} {N : ℕ} (f : Fin N → α) (i : Fin N) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  rw [List.getD_eq_getElem (List.ofFn f) d (by simpa using i.isLt), List.getElem_ofFn]

private theorem WitnessEncryption__SamplingDistribution__coordinate_list_first {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) (i : Fin m) :
    ((WitnessEncryption__SamplingDistribution__coordinateList z).getD i.val 0 : ZMod p.val) = z.1 i := by
  dsimp [WitnessEncryption__SamplingDistribution__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append _ _ _ _ (by simpa using i.isLt), WitnessEncryption__SamplingDistribution__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem WitnessEncryption__SamplingDistribution__coordinate_list_middle {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) (i : Fin m) :
    (WitnessEncryption__SamplingDistribution__coordinateList z).getD (m+i.val) 0 = (z.2.1 i).val := by
  dsimp [WitnessEncryption__SamplingDistribution__coordinateList]
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega),
    List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left]
  exact WitnessEncryption__SamplingDistribution__getD_ofFn _ i _

private theorem WitnessEncryption__SamplingDistribution__coordinate_list_last {m k : ℕ} {p : PrimeOrder}
    (z : WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) (i : Fin k) :
    ((WitnessEncryption__SamplingDistribution__coordinateList z).getD (2*m+i.val) 0 : ZMod p.val) = z.2.2 i := by
  dsimp [WitnessEncryption__SamplingDistribution__coordinateList]
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_append, List.length_ofFn]; omega)]
  simp only [List.length_append, List.length_ofFn]
  rw [show 2*m+i.val-(m+m) = i.val by omega, WitnessEncryption__SamplingDistribution__getD_ofFn]
  exact ZMod.natCast_zmod_val _

private theorem WitnessEncryption__SamplingDistribution__coordinate_card_inverse (m : ℕ) (hm : 0 < m) (p : PrimeOrder) (k : ℕ) :
    (Fintype.card (WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) : ENNReal)⁻¹ =
      ((coordinateBounds m k p.val).map (fun D : ℕ => (D : ENNReal)⁻¹)).prod := by
  letI : NeZero m := ⟨hm.ne'⟩
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hp0 : (p.val : ENNReal) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hc0 : (Fintype.card (WitnessEncryption__SamplingDistribution__CoordinateTriple m k p) : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by
    simp only [coordinateBounds, List.map_append, List.map_replicate,
      List.prod_append, List.prod_replicate]
    finiteness)).mp
  simp [WitnessEncryption__SamplingDistribution__CoordinateTriple, coordinateBounds, Fintype.card_fun,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
  <;> ring

private theorem WitnessEncryption__SamplingDistribution__exact_coordinate_list_law (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p)
    (hinj : Function.Injective (WitnessEncryption__SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)))
    (hrange : ∀ xs : List ℕ, (∃ z : WitnessEncryption__SamplingDistribution__CoordinateTriple m B.k p, WitnessEncryption__SamplingDistribution__coordinateList z = xs) ↔
      List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val))
    (xs : List ℕ) :
    ((exactCoordinates B hm).map WitnessEncryption__SamplingDistribution__coordinateList) xs =
      if List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val) then
        ((coordinateBounds m B.k p.val).map (fun D : ℕ => (D : ENNReal)⁻¹)).prod else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hx : List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val)
  · obtain ⟨z, hz⟩ := (hrange xs).mpr hx
    subst xs
    simp only [hinj.eq_iff, tsum_ite_eq', hx, ↓reduceIte]
    simpa only [exactCoordinates, PMF.uniformOfFintype_apply] using
      WitnessEncryption__SamplingDistribution__coordinate_card_inverse m hm p B.k
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

private theorem WitnessEncryption__SamplingDistribution__list_encryption_encode (m : ℕ) (p : PrimeOrder) (B : MatrixBundle m p)
    (message : Bool) (z : WitnessEncryption__SamplingDistribution__CoordinateTriple m B.k p) :
    listEncryption B message (WitnessEncryption__SamplingDistribution__coordinateList z) =
      (PMF.uniformOfFintype (Encoding p.val)).map fun σ =>
        coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message := by
  simp only [listEncryption, WitnessEncryption__SamplingDistribution__coordinate_list_first, WitnessEncryption__SamplingDistribution__coordinate_list_middle, WitnessEncryption__SamplingDistribution__coordinate_list_last]

private theorem WitnessEncryption__SamplingDistribution__list_encryption_ideal (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (message : Bool) :
    ((exactCoordinates B hm).map WitnessEncryption__SamplingDistribution__coordinateList).bind (listEncryption B message) =
      idealEncryption B hm message := by
  rw [PMF.bind_map]
  change ((exactCoordinates B hm).bind fun z => listEncryption B message (WitnessEncryption__SamplingDistribution__coordinateList z)) = _
  simp only [WitnessEncryption__SamplingDistribution__list_encryption_encode]
  change ((exactCoordinates B hm).bind fun z =>
    (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
      PMF.pure (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message)) =
    (PMF.uniformOfFintype (Encoding p.val)).bind fun σ =>
      (exactCoordinates B hm).bind fun z =>
        PMF.pure (coordinateCiphertext B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message)
  exact PMF.bind_comm _ _ _

private theorem WitnessEncryption__SamplingDistribution__sampling_success_from_codec (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (n : ℕ)
    (hinj : Function.Injective (WitnessEncryption__SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)))
    (hrange : ∀ xs : List ℕ, (∃ z : WitnessEncryption__SamplingDistribution__CoordinateTriple m B.k p, WitnessEncryption__SamplingDistribution__coordinateList z = xs) ↔
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
        ((exactCoordinates B hm).map WitnessEncryption__SamplingDistribution__coordinateList) xs := by
    change (boundedCoordinates (coordinateAttempts n m B.k) (coordinateBounds m B.k p.val))
      (some xs) = _
    rw [(bounded_coordinates_law (coordinateAttempts n m B.k)
      (coordinateBounds m B.k p.val) (WitnessEncryption__SamplingDistribution__coordinate_bounds_positive m hm p B.k)).2 xs,
      WitnessEncryption__SamplingDistribution__exact_coordinate_list_law m hm p B hinj hrange xs]
    rfl
  rw [boundedEncryption, PMF.bind_apply, WitnessEncryption__SamplingDistribution__option_tsum]
  change (samplingLaw B n) none * (PMF.pure abortCiphertext) C +
    (∑' xs, (samplingLaw B n) (some xs) * listEncryption B message xs C) = _
  simp only [PMF.pure_apply, if_neg habort, mul_zero, zero_add]
  simp_rw [hsample, mul_assoc]
  rw [ENNReal.tsum_mul_left]
  change (1 - (samplingLaw B n) none) *
    (((exactCoordinates B hm).map WitnessEncryption__SamplingDistribution__coordinateList).bind (listEncryption B message)) C = _
  rw [WitnessEncryption__SamplingDistribution__list_encryption_ideal]

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
  change Function.Injective (WitnessEncryption__SamplingDistribution__coordinateList (m := m) (k := B.k) (p := p)) at hinj
  change (∀ xs : List ℕ, (∃ z : WitnessEncryption__SamplingDistribution__CoordinateTriple m B.k p, WitnessEncryption__SamplingDistribution__coordinateList z = xs) ↔
    List.Forall₂ (fun x D : ℕ => x < D) xs (coordinateBounds m B.k p.val)) at hrange
  exact ⟨WitnessEncryption__SamplingDistribution__sampling_failure_bound m hm p B n, WitnessEncryption__SamplingDistribution__sampling_abort_mass m p B n,
    WitnessEncryption__SamplingDistribution__sampling_success_from_codec m hm p B n hinj hrange⟩

end GenericGroupWE.Main


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.BoundedEncryptionTransfer

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

-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.CommonAbort

namespace GenericGroupWE.Main
open scoped ENNReal
namespace CommonAbortProof

theorem bounded_encryption_mixture (m : ℕ) (hm : 0 < m) (p : PrimeOrder)
    (B : MatrixBundle m p) (n : ℕ) (message : Bool) (C : Ciphertext) :
    (boundedEncryption B n message) C =
      (samplingLaw B n) none*(PMF.pure abortCiphertext) C +
      (1-(samplingLaw B n) none)*(idealEncryption B hm message) C := by
  classical
  have hd := bounded_sampling_distribution m hm p B n
  cases hC : C.output with
  | none =>
    have hi := CorrectnessProof.ideal_no_output_zero m hm p B message C hC
    by_cases he : C=abortCiphertext
    · subst C
      rw [hd.2.1 message,hi]
      simp
    · rw [CorrectnessProof.bounded_no_output_zero m p B n message C hC he,hi]
      simp [PMF.pure_apply,he]
  | some out =>
    have hs : C.output.isSome := by simp [hC]
    have he : C≠abortCiphertext := by intro hh; rw [hh] at hC; simp [abortCiphertext] at hC
    rw [hd.2.2 message C hs]
    simp [PMF.pure_apply,he]

theorem mixture_bind_probability {α β : Type*} (F G H : PMF α) (s t : ENNReal)
    (hs : s≠⊤) (ht : t≠⊤) (hF : ∀ a, F a=s*G a+t*H a)
    (K : α → PMF β) (event : β → Prop) :
    probability (F.bind K) event =
      s.toReal*probability (G.bind K) event+t.toReal*probability (H.bind K) event := by
  have hm : (F.bind K).toOuterMeasure {b | event b} =
      s*(G.bind K).toOuterMeasure {b | event b}+t*(H.bind K).toOuterMeasure {b | event b} := by
    rw [PMF.toOuterMeasure_bind_apply,PMF.toOuterMeasure_bind_apply,PMF.toOuterMeasure_bind_apply]
    simp_rw [hF,add_mul,mul_assoc]
    rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
  unfold probability
  rw [hm,ENNReal.toReal_add
    (ENNReal.mul_ne_top hs (CorrectnessProof.pmf_event_finite _ _))
    (ENNReal.mul_ne_top ht (CorrectnessProof.pmf_event_finite _ _)),
    ENNReal.toReal_mul,ENNReal.toReal_mul]

theorem bounded_adversary_probability {m : ℕ} {p : PrimeOrder} {q : ℕ}
    (B : MatrixBundle m p) (n : ℕ) (A : Adversary q) (hm : 0 < m) (message : Bool) :
    probability (adversaryOutput A (boundedEncryption B n message)) (· = true) =
      samplingFailure B n*probability (adversaryOutput A (pure abortCiphertext)) (· = true) +
      (1-samplingFailure B n)*probability (adversaryOutput A (idealEncryption B hm message)) (· = true) := by
  have hδ : (samplingLaw B n) none≠⊤ := PMF.apply_ne_top _ _
  have ht : (1-(samplingLaw B n) none : ENNReal)≠⊤ := by finiteness
  have hh := mixture_bind_probability (boundedEncryption B n message) (pure abortCiphertext)
    (idealEncryption B hm message) ((samplingLaw B n) none) (1-(samplingLaw B n) none)
    hδ ht (bounded_encryption_mixture m hm p B n message)
    (fun C => (A C.public).map (fun tree => tree.run C.context)) (· = true)
  have hs : samplingFailure B n=((samplingLaw B n) none).toReal := by
    unfold samplingFailure probability
    rw [show {a | a=none}=({none} : Set (Option (List ℕ))) from rfl,
      PMF.toOuterMeasure_apply_singleton]
  simpa only [adversaryOutput,hs,ENNReal.toReal_sub_of_le ((samplingLaw B n).coe_le_one none)
    (by simp : (1 : ENNReal)≠⊤),ENNReal.toReal_one] using hh

end CommonAbortProof

theorem scheme_advantage_common_abort {m : ℕ} {p : PrimeOrder} {q : ℕ}
    (B : MatrixBundle m p) (n : ℕ) (A : Adversary q) (hm : 0 < m) :
    schemeAdvantage B n A false hm = (1-samplingFailure B n)*schemeAdvantage B n A true hm := by
  have hδ : samplingFailure B n≤1 := by
    unfold samplingFailure probability
    rw [show {a | a=none}=({none} : Set (Option (List ℕ))) from rfl,
      PMF.toOuterMeasure_apply_singleton]
    exact (ENNReal.toReal_mono (by simp) ((samplingLaw B n).coe_le_one none)).trans_eq (by simp)
  simp only [schemeAdvantage,Bool.false_eq_true,ite_false,ite_true]
  rw [CommonAbortProof.bounded_adversary_probability B n A hm false,
    CommonAbortProof.bounded_adversary_probability B n A hm true]
  rw [show samplingFailure B n*probability (adversaryOutput A (pure abortCiphertext)) (· = true)+
      (1-samplingFailure B n)*probability (adversaryOutput A (idealEncryption B hm false)) (· = true) -
      (samplingFailure B n*probability (adversaryOutput A (pure abortCiphertext)) (· = true)+
      (1-samplingFailure B n)*probability (adversaryOutput A (idealEncryption B hm true)) (· = true)) =
      (1-samplingFailure B n)*(probability (adversaryOutput A (idealEncryption B hm false)) (· = true)-
        probability (adversaryOutput A (idealEncryption B hm true)) (· = true)) by ring,
    abs_mul,abs_of_nonneg (sub_nonneg.mpr hδ)]

end GenericGroupWE.Main


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.SecurityNumerics

namespace GenericGroupWE.Main.SecurityNumerics

theorem code_universe_square (p : ℕ) : p^2≤2^labelLength p := by
  unfold labelLength
  rw [Nat.mul_comm,pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) p) 2

/-- A fixed positive residual code budget for the small-query case. -/
theorem small_capacity_and_guess (p N Q : ℕ) (hp : 2≤p) (hN : 1≤N) (hQ : Q≤N)
    (hsmall : (N : ℝ)^2/(p : ℝ)<1/16) :
    0 < p^2/2 ∧ N+1+3*Q+p^2/2≤2^labelLength p ∧
      (2 : ℝ)*(Q : ℝ)*(p : ℝ)/((p^2/2 : ℕ) : ℝ)≤8*(Q : ℝ)/(p : ℝ) ∧
      8*(Q : ℝ)/(p : ℝ)≤8*(N : ℝ)^2/(p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp0
  have hreal : (16 : ℝ)*(N : ℝ)^2<(p : ℝ) := by
    have hh := (div_lt_iff₀ hpR).mp hsmall
    nlinarith
  have hnat : 16*N^2 < p := by exact_mod_cast hreal
  have hNsquare : N≤N^2 := by nlinarith
  have hrest : N+1+3*Q≤p := by nlinarith
  let D := p^2/2
  have hmod := Nat.mod_add_div (p^2) 2
  have hrem := Nat.mod_lt (p^2) (by decide : 0<2)
  have heq : p^2=p^2%2+2*D := by simpa only [D] using hmod.symm
  have hp2 : 2*p≤p^2 := by nlinarith
  have hD : 0 < D := by omega
  have hpD : p≤D := by omega
  have h2D : 2*D≤p^2 := by omega
  have h4D : p^2≤4*D := by omega
  have hcap : N+1+3*Q+D≤2^labelLength p := by
    apply (show N+1+3*Q+D≤p^2 by omega).trans
    exact code_universe_square p
  have hDR : (0 : ℝ)<D := by exact_mod_cast hD
  have hsize : (p : ℝ)^2≤4*(D : ℝ) := by exact_mod_cast h4D
  have hdiv : (p : ℝ)/(D : ℝ)≤4/(p : ℝ) := by
    apply (div_le_div_iff₀ hDR hpR).mpr
    nlinarith
  have hguess : (2 : ℝ)*(Q : ℝ)*(p : ℝ)/(D : ℝ)≤8*(Q : ℝ)/(p : ℝ) := by
    calc
      _ = (2*(Q : ℝ))*((p : ℝ)/(D : ℝ)) := by ring
      _ ≤ (2*(Q : ℝ))*(4/(p : ℝ)) := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hQreal : (Q : ℝ)≤(N : ℝ)^2 := by exact_mod_cast hQ.trans hNsquare
  have hlast : 8*(Q : ℝ)/(p : ℝ)≤8*(N : ℝ)^2/(p : ℝ) := by
    apply (div_le_div_iff_of_pos_right hpR).mpr
    linarith
  exact ⟨hD,hcap,hguess,hlast⟩

theorem error_collection (N Q p : ℕ) (hN : 1≤N) (hQ : Q≤N) (hp : 0 < p)
    (ε : ℝ) (hε : 0≤ε) :
    ((N+1 : ℕ) : ℝ)^2*(ε+2/(p : ℝ))+16*(Q : ℝ)/(p : ℝ)≤
      24*(N : ℝ)^2*(ε+1/(p : ℝ)) := by
  have hpR : (0 : ℝ)<p := by exact_mod_cast hp
  have hNreal : (1 : ℝ)≤N := by exact_mod_cast hN
  have hQreal : (Q : ℝ)≤(N : ℝ) := by exact_mod_cast hQ
  have hH : ((N+1 : ℕ) : ℝ)^2≤4*(N : ℝ)^2 := by push_cast; nlinarith
  have hQs : (Q : ℝ)≤(N : ℝ)^2 := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_right hH (show 0≤ε+2/(p : ℝ) by positivity)
  have hsecond : 16*(Q : ℝ)/(p : ℝ)≤16*(N : ℝ)^2/(p : ℝ) := by
    apply (div_le_div_iff_of_pos_right hpR).mpr
    linarith
  calc
    _ ≤ 4*(N : ℝ)^2*(ε+2/(p : ℝ))+16*(N : ℝ)^2/(p : ℝ) := add_le_add hfirst hsecond
    _ = 24*(N : ℝ)^2*(ε+1/(p : ℝ))-20*((N : ℝ)^2*ε) := by ring
    _ ≤ _ := sub_le_self _ (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) hε))

theorem large_case_bound (p N : ℕ) (hp : 0 < p) (ε : ℝ) (hε : 0≤ε)
    (hlarge : (1 : ℝ)/16≤(N : ℝ)^2/(p : ℝ)) :
    1≤128*(N : ℝ)^2*(ε+1/(p : ℝ)) := by
  have hbase : (N : ℝ)^2/(p : ℝ)≤(N : ℝ)^2*(ε+1/(p : ℝ)) := by
    have hh : 0≤(N : ℝ)^2*ε := mul_nonneg (sq_nonneg _) hε
    calc
      _ ≤ (N : ℝ)^2/(p : ℝ)+(N : ℝ)^2*ε := le_add_of_nonneg_right hh
      _ = _ := by ring
  nlinarith

end GenericGroupWE.Main.SecurityNumerics


-- Checked public source; only private identifiers alpha-renamed: WitnessEncryption.GenericSecurity

namespace GenericGroupWE.Main.GenericSecurityProof
open scoped BigOperators

noncomputable def latentCoupledExperiment {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q) :
    PMF (ι × (Encoding p.val × (Bool × (Bool × SimulatorState p m k)))) :=
  μ.bind fun ξ => (fullCoupledExperiment (Φ ξ) Q A).map (fun out => (ξ,out))

lemma fullCoupledExperiment_sim_output {p : PrimeOrder} {m k Q : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) :
    (fullCoupledExperiment φ Q A).map (fun out => out.2.2.1)=simulator p m k Q A := by
  calc
    _ = ((fullCoupledExperiment φ Q A).map (fun out => out.2.2)).map Prod.fst := by rw [PMF.map_comp]; rfl
    _ = (fullSimulatorTrace p m k Q A).map Prod.fst := by rw [fullCoupledExperiment_sim φ A hcap]
    _ = _ := fullSimulatorTrace_output p m k Q A

lemma latentCoupledExperiment_real {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) (hOne : ∀ ξ, Φ ξ (oneCoefficient p m k)=1) :
    (latentCoupledExperiment μ Φ A).map (fun z => z.2.2.1)=μ.bind (fun ξ => physicalAdversary (Φ ξ) Q A) := by
  unfold latentCoupledExperiment
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext ξ
  exact fullCoupledExperiment_real (Φ ξ) A hcap (hOne ξ)

lemma latentCoupledExperiment_sim_output {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) :
    (latentCoupledExperiment μ Φ A).map (fun z => z.2.2.2.1)=simulator p m k Q A := by
  unfold latentCoupledExperiment
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def,fullCoupledExperiment_sim_output _ A hcap]
  exact PMF.bind_const _ _

lemma latentCoupledExperiment_sim_joint {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (hcap : m+k+1 < 2^labelLength p.val) :
    (latentCoupledExperiment μ Φ A).map (fun z => (z.1,z.2.2.2))=
      μ.bind (fun ξ => (fullSimulatorTrace p m k Q A).map (fun result => (ξ,result))) := by
  unfold latentCoupledExperiment
  simp only [PMF.map_bind,PMF.map_comp,Function.comp_def]
  congr 1
  funext ξ
  have h := congrArg (fun law : PMF (Bool × SimulatorState p m k) => law.map (fun result => (ξ,result)))
    (fullCoupledExperiment_sim (Φ ξ) A hcap)
  simpa only [PMF.map_comp,Function.comp_def] using h

lemma traceCollision_list {p : PrimeOrder} {m k : ℕ}
    (φ : Coefficient p m k →ₗ[ZMod p.val] ZMod p.val) (st : SimulatorState p m k) :
    traceCollision φ st ↔ ListCollisionProof.listCollision φ (st.entries.map Prod.fst) := by
  constructor
  · rintro ⟨a,ha,b,hb,hne,heq⟩
    exact ⟨a.1,List.mem_map.mpr ⟨a,ha,rfl⟩,b.1,List.mem_map.mpr ⟨b,hb,rfl⟩,hne,heq⟩
  · rintro ⟨a,ha,b,hb,hne,heq⟩
    obtain ⟨ea,hea,hea'⟩ := List.mem_map.mp ha
    obtain ⟨eb,heb,heb'⟩ := List.mem_map.mp hb
    exact ⟨ea,hea,eb,heb,by simpa only [hea',heb'] using hne,by simpa only [hea',heb'] using heq⟩

/-- Independent simulated transcript averaging; the latent distribution is never
conditioned on previous real noncollisions. -/
theorem latentCoupledExperiment_collision_bound {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (hbudget : m+k+1+3*Q < 2^labelLength p.val) (ε : ℝ) (hε : 0 ≤ ε)
    (hpair : ∀ a b : Coefficient p m k, a≠b → probability μ (fun ξ => Φ ξ a=Φ ξ b) ≤ ε) :
    probability (latentCoupledExperiment μ Φ A) (fun z => traceCollision (Φ z.1) z.2.2.2.2) ≤
      ((m+k+1+Q : ℕ) : ℝ)^2*ε := by
  classical
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hmap := probability_map_local (latentCoupledExperiment μ Φ A) (fun z => (z.1,z.2.2.2))
    (fun z => traceCollision (Φ z.1) z.2.2)
  rw [latentCoupledExperiment_sim_joint μ Φ A hcap] at hmap
  rw [← hmap]
  change probability (μ.bind (fun ξ => (fullSimulatorTrace p m k Q A).bind
    (fun result => PMF.pure (ξ,result)))) (fun z => traceCollision (Φ z.1) z.2.2) ≤ _
  rw [PMF.bind_comm]
  apply probability_bind_const_bound_general _ _ _ _ (by positivity)
  intro result hresult
  change probability (μ.map (fun ξ => (ξ,result))) (fun z => traceCollision (Φ z.1) z.2.2) ≤ _
  rw [probability_map_local]
  have he : (fun ξ => traceCollision (Φ ξ) result.2)=
      (fun ξ => ListCollisionProof.listCollision (Φ ξ) (result.2.entries.map Prod.fst)) := by
    funext ξ
    exact propext (traceCollision_list (Φ ξ) result.2)
  rw [he]
  apply (ListCollisionProof.fixed_list_collision_bound μ (fun ξ c => Φ ξ c) ε hε hpair
    (result.2.entries.map Prod.fst)).trans
  apply mul_le_mul_of_nonneg_right _ hε
  have hlen : (result.2.entries.map Prod.fst).length ≤ m+k+1+Q := by
    simpa only [List.length_map] using fullSimulatorTrace_length A hbudget result hresult
  have hlenR : ((result.2.entries.map Prod.fst).length : ℝ) ≤ ((m+k+1+Q : ℕ) : ℝ) := by exact_mod_cast hlen
  nlinarith [show (0 : ℝ) ≤ ((result.2.entries.map Prod.fst).length : ℝ) from Nat.cast_nonneg _,
    show (0 : ℝ) ≤ ((m+k+1+Q : ℕ) : ℝ) from Nat.cast_nonneg _]

lemma latentCoupledExperiment_guess_rate {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (D : ℕ) (hD : 0 < D) (hcapacity : m+k+1+3*Q+D ≤ 2^labelLength p.val) :
    probability (latentCoupledExperiment μ Φ A)
      (fun z => guessWithoutCollision (Φ z.1) (z.2.1,z.2.2.2)) ≤ (2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  unfold latentCoupledExperiment
  apply probability_bind_const_bound_general _ _ _ _ (by positivity)
  intro ξ hξ
  rw [probability_map_local]
  exact fullCoupledExperiment_guess_rate (Φ ξ) A D hD hcapacity

/-- Generic collision-to-security lift for a distribution of fixed affine
evaluations. Concrete fixed-test/rank estimates are supplied by the caller. -/
theorem distributional_adversary_bound {ι : Type*} {p : PrimeOrder} {m k Q : ℕ}
    (μ : PMF ι) (Φ : ι → (Coefficient p m k →ₗ[ZMod p.val] ZMod p.val)) (A : Adversary Q)
    (D : ℕ) (hD : 0 < D) (hcapacity : m+k+1+3*Q+D ≤ 2^labelLength p.val)
    (hOne : ∀ ξ, Φ ξ (oneCoefficient p m k)=1) (ε : ℝ) (hε : 0 ≤ ε)
    (hpair : ∀ a b : Coefficient p m k, a≠b → probability μ (fun ξ => Φ ξ a=Φ ξ b) ≤ ε) :
    |probability (μ.bind (fun ξ => physicalAdversary (Φ ξ) Q A)) (fun b => b=true)-
      probability (simulator p m k Q A) (fun b => b=true)| ≤
      ((m+k+1+Q : ℕ) : ℝ)^2*ε+(2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  classical
  let law := latentCoupledExperiment μ Φ A
  let bad := fun z : ι × (Encoding p.val × (Bool × (Bool × SimulatorState p m k))) =>
    traceCollision (Φ z.1) z.2.2.2.2 ∨ traceGuess z.2.1 z.2.2.2.2
  have hcap : m+k+1 < 2^labelLength p.val := by omega
  have hbudget : m+k+1+3*Q < 2^labelLength p.val := by omega
  have hbound := bool_coupling_bound law (fun z => z.2.2.1) (fun z => z.2.2.2.1) bad (by
    intro z hz hgood
    unfold law latentCoupledExperiment at hz
    obtain ⟨ξ,hξ,hz⟩ := (PMF.mem_support_bind_iff _ _ z).mp hz
    obtain ⟨out,hout,rfl⟩ := (PMF.mem_support_map_iff _ _ z).mp hz
    apply fullCoupledExperiment_agreement (Φ ξ) A hbudget out hout
    · exact fun h => hgood (Or.inl h)
    · exact fun h => hgood (Or.inr h))
  rw [latentCoupledExperiment_real μ Φ A hcap hOne,latentCoupledExperiment_sim_output μ Φ A hcap] at hbound
  have hbad : bad=(fun z => traceCollision (Φ z.1) z.2.2.2.2 ∨
      guessWithoutCollision (Φ z.1) (z.2.1,z.2.2.2)) := by
    funext z
    exact propext (by dsimp only [bad,guessWithoutCollision]; tauto)
  calc
    _ ≤ probability law bad := hbound
    _ ≤ probability law (fun z => traceCollision (Φ z.1) z.2.2.2.2)+
        probability law (fun z => guessWithoutCollision (Φ z.1) (z.2.1,z.2.2.2)) := by
      rw [hbad]
      exact probability_or_le_local _ _ _
    _ ≤ _ := add_le_add (latentCoupledExperiment_collision_bound μ Φ A hbudget ε hε hpair)
      (latentCoupledExperiment_guess_rate μ Φ A D hD hcapacity)


abbrev EncryptionCoordinates (p : PrimeOrder) (m k : ℕ) :=
  (Fin m → ZMod p.val) × (Fin m → Fin m) × (Fin k → ZMod p.val)

noncomputable def coordinateEvaluation {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (message : Bool) (z : EncryptionCoordinates p m B.k) :
    Coefficient p m B.k →ₗ[ZMod p.val] ZMod p.val :=
  evaluation p m B.k z.1 (fun j => if message then z.2.2 j else
    ∑ i : Fin m, ∑ l : Fin m, z.1 i*B.matrices j i l*(((z.2.1 l).val+1 : ℕ) : ZMod p.val))

lemma coordinateEvaluation_one {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p)
    (message : Bool) (z : EncryptionCoordinates p m B.k) :
    coordinateEvaluation B message z (oneCoefficient p m B.k)=1 := evaluation_one _ _ _ _ _

lemma coordinate_pair_test_probability {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) (hm : 0 < m)
    (message : Bool) (a b : Coefficient p m B.k) :
    probability (exactCoordinates B hm) (fun z => coordinateEvaluation B message z a=coordinateEvaluation B message z b)=
      fixedTestProbability B hm (a-b).1 (a-b).2.1 (a-b).2.2 message := by
  unfold fixedTestProbability
  congr 1
  funext z
  apply propext
  change coordinateEvaluation B message z a=coordinateEvaluation B message z b ↔
    coordinateEvaluation B message z (a-b)=0
  rw [map_sub,sub_eq_zero]

lemma coefficient_sub_nontrivial {p : PrimeOrder} {m k : ℕ} (a b : Coefficient p m k) (hab : a≠b) :
    ¬ ((a-b).1=0 ∧ (a-b).2.1=0 ∧ (a-b).2.2=0) := by
  rintro ⟨hα,hβ,hγ⟩
  apply hab
  apply sub_eq_zero.mp
  exact Prod.ext hα (Prod.ext hβ hγ)

lemma coordinate_pair_bounds {m : ℕ} {p : PrimeOrder} (B : MatrixBundle m p) (hm : 0 < m)
    (hp : m ≤ p.val) (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 → R ≤ (B.combination a).rank)
    (a b : Coefficient p m B.k) (hab : a≠b) :
    (∀ message, probability (exactCoordinates B hm) (fun z => coordinateEvaluation B message z a=coordinateEvaluation B message z b) ≤
      (m : ℝ)^(-R)+(p.val : ℝ)⁻¹) ∧
    probability (exactCoordinates B hm) (fun z => coordinateEvaluation B true z a=coordinateEvaluation B true z b) ≤
      (p.val : ℝ)⁻¹ := by
  have h := (lemma_3_4 m hm p B hp hlin R hrank (a-b).1 (a-b).2.1 (a-b).2.2).2
    (coefficient_sub_nontrivial a b hab)
  constructor
  · intro message
    rw [coordinate_pair_test_probability]
    exact h.1 message
  · rw [coordinate_pair_test_probability]
    exact h.2

lemma ideal_adversary_evaluations {m : ℕ} {p : PrimeOrder} {Q : ℕ}
    (B : MatrixBundle m p) (hm : 0 < m) (message : Bool) (A : Adversary Q) :
    adversaryOutput A (idealEncryption B hm message)=
      (exactCoordinates B hm).bind (fun z => physicalAdversary (coordinateEvaluation B message z) Q A) := by
  unfold adversaryOutput idealEncryption physicalAdversary
  rw [PMF.bind_bind]
  simp only [PMF.bind_map,Function.comp_def]
  rw [PMF.bind_comm]
  congr 1
  funext z
  congr 1
  funext σ
  rw [coordinate_public_evaluation B σ z.1 (fun i => (z.2.1 i).val+1) z.2.2 message]
  rfl


lemma ideal_security_bound {m : ℕ} {p : PrimeOrder} {Q : ℕ}
    (B : MatrixBundle m p) (hm : 0 < m) (hp : m ≤ p.val)
    (hlin : LinearIndependent (ZMod p.val) B.matrices) (R : ℝ)
    (hrank : ∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 → R ≤ (B.combination a).rank)
    (A : Adversary Q) (D : ℕ) (hD : 0 < D)
    (hcapacity : m+B.k+1+3*Q+D ≤ 2^labelLength p.val) :
    |probability (adversaryOutput A (idealEncryption B hm false)) (fun b => b=true)-
      probability (adversaryOutput A (idealEncryption B hm true)) (fun b => b=true)| ≤
      ((m+B.k+1+Q : ℕ) : ℝ)^2*((m : ℝ)^(-R)+2/(p.val : ℝ))+
        (4 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := by
  have hpow : 0 ≤ (m : ℝ)^(-R) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hf := distributional_adversary_bound (exactCoordinates B hm) (coordinateEvaluation B false) A D hD hcapacity
    (coordinateEvaluation_one B false) ((m : ℝ)^(-R)+(p.val : ℝ)⁻¹) (by positivity)
    (fun a b hab => (coordinate_pair_bounds B hm hp hlin R hrank a b hab).1 false)
  have ht := distributional_adversary_bound (exactCoordinates B hm) (coordinateEvaluation B true) A D hD hcapacity
    (coordinateEvaluation_one B true) ((p.val : ℝ)⁻¹) (by positivity)
    (fun a b hab => (coordinate_pair_bounds B hm hp hlin R hrank a b hab).2)
  rw [← ideal_adversary_evaluations B hm false A] at hf
  rw [← ideal_adversary_evaluations B hm true A] at ht
  let f := probability (adversaryOutput A (idealEncryption B hm false)) (fun b => b=true)
  let t := probability (adversaryOutput A (idealEncryption B hm true)) (fun b => b=true)
  let s := probability (simulator p m B.k Q A) (fun b => b=true)
  change |f-s| ≤ _ at hf
  change |t-s| ≤ _ at ht
  change |f-t| ≤ _
  calc
    _ ≤ |f-s|+|t-s| := by
      have h := abs_sub_le f s t
      rw [abs_sub_comm s t] at h
      exact h
    _ ≤ (((m+B.k+1+Q : ℕ) : ℝ)^2*((m : ℝ)^(-R)+(p.val : ℝ)⁻¹)+(2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ))+
        (((m+B.k+1+Q : ℕ) : ℝ)^2*((p.val : ℝ)⁻¹)+(2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ)) := add_le_add hf ht
    _ = _ := by ring

lemma schemeAdvantage_le_one {m : ℕ} {p : PrimeOrder} {Q : ℕ}
    (B : MatrixBundle m p) (n : ℕ) (A : Adversary Q) (conditional : Bool) (hm : 0 < m) :
    schemeAdvantage B n A conditional hm ≤ 1 := by
  let law := fun b => if conditional then idealEncryption B hm b else boundedEncryption B n b
  change |probability (adversaryOutput A (law false)) (fun b => b=true)-
    probability (adversaryOutput A (law true)) (fun b => b=true)| ≤ 1
  have h0 : 0 ≤ probability (adversaryOutput A (law false)) (fun b => b=true) := ENNReal.toReal_nonneg
  have h1 : 0 ≤ probability (adversaryOutput A (law true)) (fun b => b=true) := ENNReal.toReal_nonneg
  have h0' := probability_le_one_local (adversaryOutput A (law false)) (fun b => b=true)
  have h1' := probability_le_one_local (adversaryOutput A (law true)) (fun b => b=true)
  apply abs_le.mpr
  constructor <;> linarith

lemma schemeAdvantage_le_ideal {m : ℕ} {p : PrimeOrder} {Q : ℕ}
    (B : MatrixBundle m p) (n : ℕ) (A : Adversary Q) (conditional : Bool) (hm : 0 < m) :
    schemeAdvantage B n A conditional hm ≤ schemeAdvantage B n A true hm := by
  cases conditional with
  | true => exact le_rfl
  | false =>
    rw [scheme_advantage_common_abort]
    have hδ : 0 ≤ samplingFailure B n := ENNReal.toReal_nonneg
    have ha : 0 ≤ schemeAdvantage B n A true hm := abs_nonneg _
    calc
      _ ≤ 1*schemeAdvantage B n A true hm := mul_le_mul_of_nonneg_right (by linarith) ha
      _ = _ := one_mul _

end GenericGroupWE.Main.GenericSecurityProof

namespace GenericGroupWE.Main
open scoped BigOperators
open GenericSecurityProof

theorem theorem_3_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n → 16*n ≤ m →
      ∀ (p : PrimeOrder), 2^m ≤ p.val → p.val < 2^(m+1) →
      ∀ (B : MatrixBundle m p), LinearIndependent (ZMod p.val) B.matrices →
      ∀ R : ℝ,
        (∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 → R ≤ (B.combination a).rank) →
        ∀ (Q : ℕ) (A : Adversary Q) (conditional : Bool) (hm : 0 < m),
          schemeAdvantage B n A conditional hm ≤
            C * (Q + m + B.k : ℝ)^2 * ((m : ℝ)^(-R) + (p.val : ℝ)⁻¹) := by
  refine ⟨128,by norm_num,?_⟩
  intro n m hn hmn p hplower hpupper B hlin R hrank Q A conditional hm
  let N : ℕ := Q+m+B.k
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hQ : Q ≤ N := by dsimp only [N]; omega
  have hp0 : 0 < p.val := p.property.pos
  have hp2 : 2 ≤ p.val := p.property.two_le
  have hmp : m ≤ p.val := (show m < 2^m from Nat.lt_two_pow_self).le.trans hplower
  have hε : 0 ≤ (m : ℝ)^(-R) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hsmall : (N : ℝ)^2/(p.val : ℝ)<1/16
  · let D : ℕ := p.val^2/2
    obtain ⟨hD,hcap,hguess,hQguess⟩ := SecurityNumerics.small_capacity_and_guess p.val N Q hp2 hN hQ hsmall
    change 0 < D at hD
    change N+1+3*Q+D ≤ 2^labelLength p.val at hcap
    change (2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) ≤ 8*(Q : ℝ)/(p.val : ℝ) at hguess
    have hcapacity : m+B.k+1+3*Q+D ≤ 2^labelLength p.val := by dsimp only [N] at hcap; omega
    have hideal := ideal_security_bound B hm hmp hlin R hrank A D hD hcapacity
    have hhead : m+B.k+1+Q=N+1 := by dsimp only [N]; omega
    rw [hhead] at hideal
    have hguess2 : (4 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) ≤ 16*(Q : ℝ)/(p.val : ℝ) := by
      calc
        _ = 2*((2 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ)) := by ring
        _ ≤ 2*(8*(Q : ℝ)/(p.val : ℝ)) := mul_le_mul_of_nonneg_left hguess (by norm_num)
        _ = _ := by ring
    have h24 : schemeAdvantage B n A true hm ≤ 24*(N : ℝ)^2*((m : ℝ)^(-R)+(p.val : ℝ)⁻¹) := by
      change |probability (adversaryOutput A (idealEncryption B hm false)) (fun b => b=true)-
        probability (adversaryOutput A (idealEncryption B hm true)) (fun b => b=true)| ≤ _
      calc
        _ ≤ ((N+1 : ℕ) : ℝ)^2*((m : ℝ)^(-R)+2/(p.val : ℝ))+(4 : ℝ)*(Q : ℝ)*(p.val : ℝ)/(D : ℝ) := hideal
        _ ≤ ((N+1 : ℕ) : ℝ)^2*((m : ℝ)^(-R)+2/(p.val : ℝ))+16*(Q : ℝ)/(p.val : ℝ) := by linarith
        _ ≤ _ := by simpa only [one_div] using SecurityNumerics.error_collection N Q p.val hN hQ hp0 ((m : ℝ)^(-R)) hε
    have hnonneg : 0 ≤ (N : ℝ)^2*((m : ℝ)^(-R)+(p.val : ℝ)⁻¹) := by positivity
    have hconst := mul_le_mul_of_nonneg_right (by norm_num : (24 : ℝ) ≤ 128) hnonneg
    have h128 : schemeAdvantage B n A true hm ≤ 128*(N : ℝ)^2*((m : ℝ)^(-R)+(p.val : ℝ)⁻¹) :=
      h24.trans (by simpa only [mul_assoc] using hconst)
    have hall := (schemeAdvantage_le_ideal B n A conditional hm).trans h128
    simpa only [N,Nat.cast_add] using hall
  · have hlarge : (1 : ℝ)/16 ≤ (N : ℝ)^2/(p.val : ℝ) := le_of_not_gt hsmall
    have hnum := SecurityNumerics.large_case_bound p.val N hp0 ((m : ℝ)^(-R)) hε hlarge
    have hall := (schemeAdvantage_le_one B n A conditional hm).trans hnum
    simpa only [N,Nat.cast_add,one_div] using hall

end GenericGroupWE.Main

open scoped BigOperators
open GenericGroupWE.Main

theorem solution :
∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ), 2 ≤ n → 16*n ≤ m →
      ∀ (p : PrimeOrder), 2^m ≤ p.val → p.val < 2^(m+1) →
      ∀ (B : MatrixBundle m p), LinearIndependent (ZMod p.val) B.matrices →
      ∀ R : ℝ,
        (∀ a : Fin B.k → ZMod p.val, B.combination a ≠ 0 → R ≤ (B.combination a).rank) →
        ∀ (Q : ℕ) (A : Adversary Q) (conditional : Bool) (hm : 0 < m),
          schemeAdvantage B n A conditional hm ≤
            C * (Q + m + B.k : ℝ)^2 * ((m : ℝ)^(-R) + (p.val : ℝ)⁻¹) :=
  @GenericGroupWE.Main.theorem_3_5
