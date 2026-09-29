-- Prove2me | solution 1 for Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1aab7de7-dccd-55b2-9678-65cd053e958b

import Mathlib
import Definitions.Def_Patching_SystemTypes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing

open IsLocalRing RingTheory

namespace Ws14Port

universe u v

open IsLocalRing RingTheory RingTheory.Sequence Module

section

variable (R S M : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
variable [AddCommGroup M] [Module R M] [Module S M] [Algebra R S] [IsScalarTower R S M]
variable [IsLocalHom (algebraMap R S)]

p2m_open "IsLocalRing Module.IsLocalRing RingTheory Module RingTheory.Sequence"

noncomputable section

scoped instance instSubsingletonQuotientOfSubsingleton [Subsingleton M] (N : Submodule R M) : Subsingleton (M ⧸ N) :=
  Function.Surjective.subsingleton N.mkQ_surjective

lemma Module.length_le_depth (s : List R)
    (hs : Sequence.IsWeaklyRegular M s) (hs' : ∀ r ∈ s, r ∈ maximalIdeal R) :
    s.length ≤ Module.depth R M :=
  le_sSup ⟨s, hs, hs', rfl⟩

lemma Module.depth_of_subsingleton [Subsingleton M] :
    Module.depth R M = ⊤ := by
  rw [Module.depth, sSup_eq_top]
  rintro b hb
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hb.ne
  simp only [Set.mem_setOf_eq, exists_prop, ↓existsAndEq, and_true, Nat.cast_lt]
  refine ⟨List.replicate b.succ 0, ⟨?_, ?_⟩, ?_⟩
  · refine  (Sequence.isWeaklyRegular_iff_Fin ..).mpr fun i ↦ ?_
    exact fun _ _ _ ↦ Subsingleton.elim _ _
  · simp
  · simp

lemma Module.depth_of_isScalarTower :
    Module.depth R M ≤ Module.depth S M := by
  refine sSup_le_sSup ?_
  rintro _ ⟨s, hs₁, hs₂, rfl⟩
  rw [← Sequence.isWeaklyRegular_map_algebraMap_iff S M s] at hs₁
  exact ⟨_, hs₁, by simpa, by simp⟩

@[stacks 00LK]
lemma Module.depth_le_krullDim_support [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ Order.krullDim (Module.support R M) := by
  have : Nonempty (Module.support R M) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty,
      ne_eq, support_eq_empty_iff, not_subsingleton_iff_nontrivial]
  cases h : Order.krullDim (Module.support R M) with
  | bot => simpa using Order.krullDim_nonneg.trans_eq h
  | coe n =>
  cases n with
  | top => simp
  | coe n =>
  clear this
  simp only [WithBot.coe_le_coe, ge_iff_le]
  induction n using Nat.strong_induction_on generalizing M with
  | h n IH =>
    rw [depth, sSup_le_iff]
    rintro _ ⟨l, hl, hl', rfl⟩
    apply WithTop.coe_le_coe.mpr ?_
    cases l with
    | nil => simp
    | cons x l =>
    simp only [Sequence.isWeaklyRegular_cons_iff] at hl
    have : Nontrivial (QuotSMulTop x M) := by
      apply Submodule.Quotient.nontrivial_iff.2
      rw [← Submodule.ideal_span_singleton_smul, ne_comm]
      apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      refine le_trans ?_ (maximalIdeal_le_jacobson _)
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hl' _ (by simp)
    rw [Module.support_eq_zeroLocus, ← ringKrullDim_quotient] at h
    let f : (R ⧸ annihilator R M) ⧸ Ideal.span {(Ideal.Quotient.mk (annihilator R M)) x} →+*
        R ⧸ annihilator R (QuotSMulTop x M) :=
      Ideal.Quotient.lift _ (Ideal.quotientMap _ (.id R)
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
        (show Ideal.span _ ≤ RingHom.ker _ by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          simp only [SetLike.mem_coe, RingHom.mem_ker, Ideal.quotientMap_mk, RingHom.id_apply,
            Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
          intro m
          obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact ⟨m, trivial, rfl⟩)
    have hf : Function.Surjective f := by
      apply Ideal.Quotient.lift_surjective_of_surjective
      apply Ideal.Quotient.lift_surjective_of_surjective
      exact Ideal.Quotient.mk_surjective
    have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := R ⧸ annihilator R M) (r := x) (by
      rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]
      intro z hz
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      simp only [← map_mul, Ideal.Quotient.eq_zero_iff_mem,
        Module.mem_annihilator] at hz ⊢
      intro m
      apply hl.1
      simpa [smul_comm x, mul_smul] using hz m)
    rw [h] at this
    replace this := (add_le_add (ringKrullDim_le_of_surjective f hf) le_rfl).trans this
    cases h : ringKrullDim (R ⧸ annihilator R (QuotSMulTop x M)) with
    | bot =>
      have : Nontrivial (R ⧸ annihilator R (QuotSMulTop x M)) := by
        rw [Ideal.Quotient.nontrivial_iff, ← Submodule.annihilator_top, ne_eq,
          Submodule.annihilator_eq_top_iff]
        exact top_ne_bot
      have := ringKrullDim_nonneg_of_nontrivial.trans_eq h
      simp at this
    | coe m =>
    cases m with
    | top =>
      have : (⊤ : ℕ∞) ≤ (n : ℕ) := by apply WithBot.coe_le_coe.mp; (simp only [h] at this; exact this)
      cases (ENat.coe_lt_top n).not_ge this
    | coe m =>
    rw [h] at this
    replace this : m + 1 ≤ n := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp this)
    replace IH := IH m (Nat.lt_of_succ_le this) (QuotSMulTop x M)
      (by rwa [Module.support_eq_zeroLocus, ← ringKrullDim_quotient])
    replace IH := WithTop.coe_le_coe.mp
      ((Module.length_le_depth _ _ l hl.2 (by simp_all)).trans IH)
    · simp only [List.length_cons, ge_iff_le]
      linarith

lemma Module.depth_le_dim_annihilator
    [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ Module.annihilator R M) := by
  rw [ringKrullDim_quotient, ← Module.support_eq_zeroLocus]
  exact Module.depth_le_krullDim_support _ _

lemma Module.depth_le_dim [Nontrivial M] [Module.Finite R M] :
    .some (Module.depth R M) ≤ ringKrullDim R :=
  (depth_le_dim_annihilator R M).trans (ringKrullDim_quotient_le _)

lemma isSMulRegular_iff_of_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  constructor
  · intro H m n h
    have i : I := Nonempty.some inferInstance
    have := @H (m • b i) (n • b i) (by simp_all [← mul_smul])
    simpa using congr(b.repr $this i)
  · intro H m n h
    apply b.repr.injective
    ext i
    replace h := congr(b.repr $h i)
    simp only [map_smul] at h
    exact H h

lemma RingTheory.Sequence.isWeaklyRegular_of_subsingleton
    {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Subsingleton R] (s : List R) : Sequence.IsWeaklyRegular M s :=
  have : Subsingleton M := Module.subsingleton R M
  (isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _

open scoped Pointwise TensorProduct in
lemma RingTheory.Sequence.isWeaklyRegular_of_free_aux
    {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {s : List R} :
      Sequence.IsWeaklyRegular M s ↔ Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · simp [RingTheory.Sequence.isWeaklyRegular_of_subsingleton]
    exact IH (by simp_all)

lemma RingTheory.Sequence.isWeaklyRegular_of_free
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {s : List R} :
      Sequence.IsWeaklyRegular M s ↔ Sequence.IsWeaklyRegular R s := by
  let b := Module.Free.chooseBasis R M
  have : Nontrivial R := Module.nontrivial R M
  rw [b.repr.isWeaklyRegular_congr, isWeaklyRegular_of_free_aux]

lemma Module.depth_le_of_free [Module.Free R M] : Module.depth R R ≤ Module.depth R M := by
  cases subsingleton_or_nontrivial M
  · simp [Module.depth_of_subsingleton]
  apply sSup_le_sSup
  rintro _ ⟨s, hs, hs', rfl⟩
  refine ⟨s, Ws14Port.RingTheory.Sequence.isWeaklyRegular_of_free.mpr hs, hs', rfl⟩

lemma Module.faithfulSMul_of_depth_eq_ringKrullDim [IsDomain R] [Nontrivial M] [Module.Finite R M]
    (H : ringKrullDim R < ⊤) (H' : .some (Module.depth R M) = ringKrullDim R) :
    FaithfulSMul R M := by
  have : Nontrivial (R ⧸ annihilator R M) := Ideal.Quotient.nontrivial_iff.2
    (by rw [ne_eq, ← Submodule.annihilator_top, Submodule.annihilator_eq_top_iff]
        exact top_ne_bot)
  rw [← Module.annihilator_eq_bot]
  by_contra H''
  apply (le_refl ((.some (Module.depth R M)) : WithBot ℕ∞)).not_gt
  calc
    _ ≤ ringKrullDim (R ⧸ annihilator R M) := Module.depth_le_dim_annihilator _ _
    _ < ringKrullDim R := by
      simp only [ringKrullDim, Order.krullDim_eq_iSup_length,
        WithBot.coe_lt_coe]
      rw [← ENat.add_one_le_iff, ENat.iSup_add, iSup_le_iff]
      · intro l
        let l' : LTSeries (PrimeSpectrum R) := (l.map
          (PrimeSpectrum.comap (Ideal.Quotient.mk _)) ?_).cons ⊥ ?_
        · refine le_trans ?_ (le_iSup _ l')
          change _ ≤ ((0 + l.length + 1 : ℕ) : ℕ∞)
          simp
        · intros I J
          change I < J → I.asIdeal.comap _ < J.asIdeal.comap _
          simp [lt_iff_le_not_ge, ← Ideal.map_le_iff_le_comap,
            Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
        · refine (bot_lt_iff_ne_bot.mpr H'').trans_le ?_
          conv_lhs => rw [← Ideal.mk_ker (I := annihilator R M), RingHom.ker]
          exact Ideal.comap_mono bot_le
      · rw [← lt_top_iff_ne_top]
        apply WithBot.coe_lt_coe.mp
        rw [← Order.krullDim_eq_iSup_length, ← ringKrullDim]
        refine (ringKrullDim_quotient_le _).trans_lt H
    _ = .some (Module.depth R M) := H'.symm

end

end

section

p2m_open "IsLocalRing Module.IsLocalRing PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"
open scoped Pointwise

noncomputable section

namespace PowerSeries
open PowerSeries

variable {R : Type*} [CommRing R]

lemma isSMulRegular_X : IsSMulRegular R⟦X⟧ (X : R⟦X⟧) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  simpa only [coeff_succ_X_mul] using congrArg (coeff (n + 1)) h

lemma ker_constantCoeff : RingHom.ker (constantCoeff (R := R)) = Ideal.span {(X : R⟦X⟧)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

def quotSpanXEquiv : (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

@[scoped simp]
lemma quotSpanXEquiv_mk (f : R⟦X⟧) :
    quotSpanXEquiv (Ideal.Quotient.mk _ f) = constantCoeff f := by
  simp only [quotSpanXEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq]
  rfl

lemma smul_top_eq_span_X :
    (X : R⟦X⟧) • (⊤ : Ideal R⟦X⟧) = Ideal.span {(X : R⟦X⟧)} := by
  rw [← Submodule.ideal_span_singleton_smul]
  simp

section IsLocalRing

variable [IsLocalRing R]

scoped instance instIsLocalRingPowerSeries' : IsLocalRing R⟦X⟧ := inferInstanceAs (IsLocalRing (MvPowerSeries Unit R))

lemma mem_maximalIdeal_iff {f : R⟦X⟧} :
    f ∈ maximalIdeal R⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff]

lemma X_mem_maximalIdeal : (X : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rw [mem_maximalIdeal_iff, constantCoeff_X]
  exact zero_mem _

lemma C_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    (C r : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rwa [mem_maximalIdeal_iff, constantCoeff_C]

end IsLocalRing

def quotXSMulTopAddEquiv : QuotSMulTop (X : R⟦X⟧) R⟦X⟧ ≃+ R :=
  ((Ideal.quotEquivOfEq smul_top_eq_span_X).trans quotSpanXEquiv).toAddEquiv

@[scoped simp]
lemma quotXSMulTopAddEquiv_mk (f : R⟦X⟧) :
    quotXSMulTopAddEquiv (Submodule.Quotient.mk f) = constantCoeff f := by
  show quotSpanXEquiv ((Ideal.quotEquivOfEq smul_top_eq_span_X) (Submodule.Quotient.mk f)) =
    constantCoeff f
  simp only [Ideal.quotEquivOfEq]
  rfl

lemma quotXSMulTopAddEquiv_smul (r : R) (m : QuotSMulTop (X : R⟦X⟧) R⟦X⟧) :
    quotXSMulTopAddEquiv ((C r : R⟦X⟧) • m) = r • quotXSMulTopAddEquiv m := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [← Submodule.Quotient.mk_smul, quotXSMulTopAddEquiv_mk, quotXSMulTopAddEquiv_mk,
    smul_eq_mul, smul_eq_mul, map_mul, constantCoeff_C]

lemma isWeaklyRegular_X_cons_map_C {s : List R} (hs : Sequence.IsWeaklyRegular R s) :
    Sequence.IsWeaklyRegular R⟦X⟧ ((X : R⟦X⟧) :: s.map C) := by
  rw [Sequence.isWeaklyRegular_cons_iff]
  refine ⟨isSMulRegular_X, ?_⟩
  rw [AddEquiv.isWeaklyRegular_congr (e := quotXSMulTopAddEquiv)
    (bs := s) (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr
      fun r _ m ↦ quotXSMulTopAddEquiv_smul r m))]
  exact hs

section Depth

variable (R) [IsLocalRing R]

lemma le_depth_of_isWeaklyRegular {s : List R} (hs : Sequence.IsWeaklyRegular R s)
    (hs' : ∀ r ∈ s, r ∈ maximalIdeal R) :
    (s.length : ℕ∞) + 1 ≤ Module.depth R⟦X⟧ R⟦X⟧ := by
  have key := Module.length_le_depth R⟦X⟧ R⟦X⟧ ((X : R⟦X⟧) :: s.map C)
    (isWeaklyRegular_X_cons_map_C hs) ?_
  · simpa [add_comm] using key
  · rintro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact X_mem_maximalIdeal
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact C_mem_maximalIdeal (hs' a ha)

lemma natCast_succ_le_depth {d : ℕ} (hd : (d : ℕ∞) ≤ Module.depth R R) :
    ((d + 1 : ℕ) : ℕ∞) ≤ Module.depth R⟦X⟧ R⟦X⟧ := by
  obtain ⟨s, hs, hs', hlen⟩ : ∃ s : List R, Sequence.IsWeaklyRegular R s ∧
      (∀ r ∈ s, r ∈ maximalIdeal R) ∧ d ≤ s.length := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exact ⟨[], (Sequence.isWeaklyRegular_iff_Fin _ _).mpr (fun i ↦ i.elim0),
        by simp, Nat.zero_le _⟩
    · have hlt : ((d - 1 : ℕ) : ℕ∞) < Module.depth R R :=
        lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.sub_lt hd0 one_pos)) hd
      rw [Module.depth, lt_sSup_iff] at hlt
      obtain ⟨b, ⟨s, hs, hs', rfl⟩, hb⟩ := hlt
      refine ⟨s, hs, hs', ?_⟩
      have hlen' : (d - 1 : ℕ) < s.length := Nat.cast_lt.mp hb
      omega
  refine le_trans ?_ (le_depth_of_isWeaklyRegular R hs hs')
  have key : ((d + 1 : ℕ) : ℕ∞) ≤ ((s.length + 1 : ℕ) : ℕ∞) :=
    Nat.cast_le.mpr (Nat.succ_le_succ hlen)
  simpa [Nat.cast_add] using key

end Depth

section KrullDim

variable (R) [IsNoetherianRing R] [IsLocalRing R]

lemma ringKrullDim_powerSeries : ringKrullDim R⟦X⟧ = ringKrullDim R + 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := R⟦X⟧) (x := X) isSMulRegular_X X_mem_maximalIdeal
  rw [ringKrullDim_eq_of_ringEquiv (quotSpanXEquiv (R := R))] at h
  exact h.symm

end KrullDim

end PowerSeries
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

namespace IsLocalRing
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing"

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth R R = d

namespace IsCohenMacaulayOfDim
open IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma ringKrullDim_eq (h : IsCohenMacaulayOfDim R d) : ringKrullDim R = d := h.1

lemma depth_eq (h : IsCohenMacaulayOfDim R d) : Module.depth R R = d := h.2

lemma ringKrullDim_lt_top [IsNoetherianRing R] (_ : IsCohenMacaulayOfDim R d) :
    ringKrullDim R < ⊤ :=
  _root_.ringKrullDim_lt_top

lemma patching_hypotheses {Λ Rₒₒ : Type*} [CommRing Λ] [IsLocalRing Λ] [CommRing Rₒₒ]
    [IsLocalRing Rₒₒ] [IsNoetherianRing Rₒₒ]
    (hΛ : IsCohenMacaulayOfDim Λ d) (hR : IsCohenMacaulayOfDim Rₒₒ d) :
    ringKrullDim Rₒₒ < ⊤ ∧ .some (Module.depth Λ Λ) = ringKrullDim Rₒₒ := by
  refine ⟨hR.ringKrullDim_lt_top, ?_⟩
  rw [hR.ringKrullDim_eq, hΛ.depth_eq]
  rfl

lemma Module.depth_le_depth_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Module.depth R R ≤ Module.depth S S := by
  refine sSup_le_sSup ?_
  rintro _ ⟨s, hs, hs', rfl⟩
  refine ⟨s.map e, ?_, ?_, by simp⟩
  · exact (AddEquiv.isWeaklyRegular_congr (e := e.toAddEquiv)
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
        fun r _ x ↦ by simp [smul_eq_mul]))).mp hs
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal a).mp (hs' a ha))
      (by simpa using hu.map e.symm.toRingHom)

lemma of_ringEquiv {S : Type*} [CommRing S] [IsLocalRing S] (e : R ≃+* S)
    (h : IsCohenMacaulayOfDim R d) : IsCohenMacaulayOfDim S d := by
  refine ⟨(ringKrullDim_eq_of_ringEquiv e).symm.trans h.1, le_antisymm ?_ ?_⟩
  · exact (Module.depth_le_depth_of_ringEquiv e.symm).trans (le_of_eq h.2)
  · exact (le_of_eq h.2.symm).trans (Module.depth_le_depth_of_ringEquiv e)

lemma of_field (K : Type*) [Field K] : IsCohenMacaulayOfDim K 0 := by
  refine ⟨by rw [ringKrullDim_eq_zero_of_field K]; rfl, le_antisymm ?_ (by simp)⟩
  have h := Module.depth_le_dim K K
  rw [ringKrullDim_eq_zero_of_field K] at h
  exact_mod_cast h

lemma of_isDiscreteValuationRing (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞]
    [IsDiscreteValuationRing 𝓞] : IsCohenMacaulayOfDim 𝓞 1 := by
  have hdim : ringKrullDim 𝓞 = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one 𝓞 (IsDiscreteValuationRing.not_isField 𝓞)
  refine ⟨by exact_mod_cast hdim, le_antisymm ?_ ?_⟩
  · have h := Module.depth_le_dim 𝓞 𝓞
    rw [hdim] at h
    exact_mod_cast h
  ·
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝓞
    have hreg : Sequence.IsWeaklyRegular 𝓞 [π] := by
      rw [show [π] = π :: ([] : List 𝓞) from rfl, Sequence.isWeaklyRegular_cons_iff]
      refine ⟨fun a b h ↦ mul_left_cancel₀ hπ.ne_zero ?_,
        (Sequence.isWeaklyRegular_iff_Fin _ _).mpr (fun i ↦ i.elim0)⟩
      simpa only [smul_eq_mul] using h
    have hmem : ∀ r ∈ [π], r ∈ maximalIdeal 𝓞 := by
      intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      rw [hπ.maximalIdeal_eq]
      exact Ideal.subset_span rfl
    simpa using Module.length_le_depth 𝓞 𝓞 [π] hreg hmem

end IsCohenMacaulayOfDim
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end IsLocalRing
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

namespace PowerSeries
open PowerSeries

p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing"

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem isCohenMacaulayOfDim_succ {d : ℕ} (h : IsCohenMacaulayOfDim R d) :
    IsCohenMacaulayOfDim R⟦X⟧ (d + 1) := by
  have hdim : ringKrullDim R⟦X⟧ = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_powerSeries, h.ringKrullDim_eq]
    push_cast
    rfl
  refine ⟨hdim, le_antisymm ?_ ?_⟩
  · have hle := Module.depth_le_dim R⟦X⟧ R⟦X⟧
    rw [hdim] at hle
    exact_mod_cast hle
  · exact natCast_succ_le_depth R (le_of_eq h.depth_eq.symm)

end PowerSeries
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section

p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"

section DepthCharacterization

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

lemma Module.exists_isSMulRegular_of_depth_pos (h : 0 < Module.depth R M) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  obtain ⟨b, hb, hpos⟩ := lt_sSup_iff.mp h
  obtain ⟨s, hreg, hmem, rfl⟩ := hb
  cases s with
  | nil => simp at hpos
  | cons x rest =>
      rw [Sequence.isWeaklyRegular_cons_iff] at hreg
      exact ⟨x, hmem x (by simp), hreg.1⟩

lemma Module.depth_pos_of_isSMulRegular {x : R} (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular M x) : 0 < Module.depth R M := by
  have h1 : (1 : ℕ∞) ≤ Module.depth R M := by
    simpa using Module.length_le_depth R M [x]
      ((Sequence.isWeaklyRegular_singleton_iff M x).mpr hreg) (by simpa using hx)
  exact zero_lt_one.trans_le h1

lemma Module.depth_pos_iff_exists_isSMulRegular :
    0 < Module.depth R M ↔ ∃ x ∈ maximalIdeal R, IsSMulRegular M x :=
  ⟨Module.exists_isSMulRegular_of_depth_pos R M, fun ⟨_, hx, hreg⟩ =>
    Module.depth_pos_of_isSMulRegular R M hx hreg⟩

lemma Module.maximalIdeal_ne_bot_of_depth_pos [Nontrivial M] (h : 0 < Module.depth R M) :
    maximalIdeal R ≠ ⊥ := by
  obtain ⟨x, hxm, hreg⟩ := Module.exists_isSMulRegular_of_depth_pos R M h
  intro hbot
  rw [hbot, Submodule.mem_bot] at hxm
  subst hxm
  obtain ⟨a, b, hab⟩ := exists_pair_ne M
  exact hab (hreg (by simp))

lemma IsLocalRing.maximalIdeal_ne_bot_of_ringKrullDim_pos (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ≠ ⊥ := by
  intro hbot
  rw [ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)] at hdim
  exact hdim.false

lemma Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos [IsNoetherianRing R]
    (h : 0 < Module.depth R M) : maximalIdeal R ∉ associatedPrimes R M := by
  intro hmem
  obtain ⟨x, hxm, hreg⟩ := Module.exists_isSMulRegular_of_depth_pos R M h
  have hx_in : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := Set.mem_biUnion hmem hxm
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at hx_in
  exact hx_in hreg

end DepthCharacterization
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section PrimeAvoidance

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_notMem_associatedPrimes
    (hR : maximalIdeal R ∉ associatedPrimes R R)
    (hM : maximalIdeal R ∉ associatedPrimes R M)
    (hbot : maximalIdeal R ≠ ⊥) :
    ∃ x ∈ maximalIdeal R,
      x ∉ (maximalIdeal R) ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x := by
  classical

  have hfin : (insert ((maximalIdeal R) ^ 2)
      (associatedPrimes R R ∪ associatedPrimes R M)).Finite :=
    Set.Finite.insert _ ((associatedPrimes.finite R R).union (associatedPrimes.finite R M))

  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_union] at hIs
    rcases hIs with rfl | hI | hI
    ·
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    ·
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal (AssociatedPrimes.mem_iff.mp hI).isPrime.ne_top).antisymm
          hle
      exact hR (heq ▸ hI)
    ·
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal (AssociatedPrimes.mem_iff.mp hI).isPrime.ne_top).antisymm
          hle
      exact hM (heq ▸ hI)

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff, Set.mem_union] at hIs
    rcases hIs with rfl | hI | hI
    · exact absurd rfl hI₁
    · exact (AssociatedPrimes.mem_iff.mp hI).isPrime
    · exact (AssociatedPrimes.mem_iff.mp hI).isPrime

  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_, ?_⟩
  ·
    intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  ·
    have hxnot : x ∉ ⋃ p ∈ associatedPrimes R R, (p : Set R) := fun hx =>
      hxout (Set.biUnion_subset_biUnion_left (fun p hp =>
        Set.mem_insert_of_mem _ (Set.mem_union_left _ hp)) hx)
    rw [biUnion_associatedPrimes_eq_compl_regular R R] at hxnot
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hxnot
  ·
    have hxnot : x ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := fun hx =>
      hxout (Set.biUnion_subset_biUnion_left (fun p hp =>
        Set.mem_insert_of_mem _ (Set.mem_union_right _ hp)) hx)
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hxnot
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hxnot

end PrimeAvoidance
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

theorem Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : 0 < Module.depth R R) (hM : 0 < Module.depth R M) :
    ∃ x ∈ maximalIdeal R,
      x ∉ (maximalIdeal R) ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x :=
  IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_notMem_associatedPrimes R M
    (Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos R R hR)
    (Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos R M hM)
    (Module.maximalIdeal_ne_bot_of_depth_pos R R hR)

theorem Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos'
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : 0 < Module.depth R R) (hM : 0 < Module.depth R M)
    (_hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R,
      x ∉ (maximalIdeal R) ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x :=
  Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos R M hR hM

theorem IsLocalRing.IsCohenMacaulayOfDim.exists_isSMulRegular_and_isSMulRegular
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
    (hCM : IsCohenMacaulayOfDim R d)
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hd : 0 < d) (hM : 0 < Module.depth R M) :
    ∃ x ∈ maximalIdeal R,
      x ∉ (maximalIdeal R) ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x := by
  refine Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos R M ?_ hM
  rw [hCM.depth_eq]
  exact_mod_cast hd

theorem Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos_of_isDomain
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : 0 < Module.depth R M) (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R,
      x ∉ (maximalIdeal R) ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x := by
  refine Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos R M ?_ hM

  obtain ⟨y, hym, hy0⟩ := (Submodule.ne_bot_iff _).mp
    (IsLocalRing.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim)
  refine Module.depth_pos_of_isSMulRegular R R hym ?_
  intro a b hab
  exact mul_left_cancel₀ hy0 (by simpa only [smul_eq_mul] using hab)

theorem IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_isDiscreteValuationRing
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞]
    (M : Type*) [AddCommGroup M] [Module 𝓞 M] [Module.Finite 𝓞 M]
    (hM : 0 < Module.depth 𝓞 M) :
    ∃ x ∈ maximalIdeal 𝓞,
      x ∉ (maximalIdeal 𝓞) ^ 2 ∧ IsSMulRegular 𝓞 x ∧ IsSMulRegular M x :=
  (IsCohenMacaulayOfDim.of_isDiscreteValuationRing 𝓞).exists_isSMulRegular_and_isSMulRegular
    M Nat.one_pos hM

example (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] :
    ∃ x ∈ maximalIdeal 𝓞,
      x ∉ (maximalIdeal 𝓞) ^ 2 ∧ IsSMulRegular 𝓞 x ∧ IsSMulRegular 𝓞 x := by
  refine IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_isDiscreteValuationRing 𝓞 𝓞 ?_
  rw [(IsCohenMacaulayOfDim.of_isDiscreteValuationRing 𝓞).depth_eq]
  exact_mod_cast Nat.one_pos

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section

p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory Submodule Pointwise"

noncomputable section

namespace Module
open Module

variable {R : Type*} [CommRing R] [IsLocalRing R]

section Transport

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

lemma depth_eq_of_linearEquiv (e : M ≃ₗ[R] N) : Module.depth R M = Module.depth R N := by
  rw [Module.depth, Module.depth]
  congr 1
  ext k
  constructor
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mp hs, hs', rfl⟩
  · rintro ⟨s, hs, hs', rfl⟩
    exact ⟨s, (e.isWeaklyRegular_congr s).mpr hs, hs', rfl⟩

lemma exists_isWeaklyRegular_of_le_depth (M : Type*) [AddCommGroup M] [Module R M]
    (n : ℕ) (hn : (n : ℕ∞) ≤ Module.depth R M) :
    ∃ s : List R, Sequence.IsWeaklyRegular M s ∧ (∀ r ∈ s, r ∈ maximalIdeal R) ∧
      s.length = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨[], Sequence.IsWeaklyRegular.nil R M, by simp, rfl⟩
  · have hlt : ((n - 1 : ℕ) : ℕ∞) < Module.depth R M :=
      lt_of_lt_of_le (Nat.cast_lt.mpr (by omega)) hn
    rw [Module.depth, lt_sSup_iff] at hlt
    obtain ⟨b, ⟨s, hs, hs', rfl⟩, hb⟩ := hlt
    have hlen : n ≤ s.length := by
      have := Nat.cast_lt.mp hb
      omega
    refine ⟨s.take n, ?_, ?_, ?_⟩
    · exact ((Sequence.isWeaklyRegular_append_iff M (s.take n) (s.drop n)).mp
        (by rwa [List.take_append_drop])).1
    · exact fun r hr => hs' r (List.take_subset n s hr)
    · rw [List.length_take]; omega

variable (M) in

lemma depth_lt_top [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] :
    Module.depth R M < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hle := Module.depth_le_dim R M
  rw [h, WithBot.coe_top, top_le_iff] at hle
  exact (ringKrullDim_lt_top (R := R)).ne hle

def quotSMulTopQuotSMulTopEquivSup (M : Type*) [AddCommGroup M] [Module R M] (z x : R) :
    QuotSMulTop x (QuotSMulTop z M) ≃ₗ[R]
      M ⧸ (z • (⊤ : Submodule R M) ⊔ x • (⊤ : Submodule R M)) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ])).trans
    (Submodule.quotientQuotientEquivQuotientSup (z • ⊤) (x • ⊤))

def quotSMulTopQuotSMulTopComm (M : Type*) [AddCommGroup M] [Module R M] (x z : R) :
    QuotSMulTop x (QuotSMulTop z M) ≃ₗ[R] QuotSMulTop z (QuotSMulTop x M) :=
  (quotSMulTopQuotSMulTopEquivSup M z x).trans <|
    (Submodule.quotEquivOfEq _ _ (sup_comm _ _)).trans
      (quotSMulTopQuotSMulTopEquivSup M x z).symm

end Transport
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Elementary

variable {M : Type*} [AddCommGroup M] [Module R M]

lemma eq_zero_of_maximalIdeal_smul_eq_zero {x y₁ y₂ : R} (hxreg : IsSMulRegular M x)
    (hy : Sequence.IsWeaklyRegular M [y₁, y₂])
    (hy₁ : y₁ ∈ maximalIdeal R) (hy₂ : y₂ ∈ maximalIdeal R)
    (m₀ : QuotSMulTop x M) (hm₀ : ∀ a ∈ maximalIdeal R, a • m₀ = 0) : m₀ = 0 := by
  rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_singleton_iff] at hy
  obtain ⟨hy₁reg, hy₂reg⟩ := hy
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m₀
  rw [Submodule.Quotient.mk_eq_zero]

  have key : ∀ a ∈ maximalIdeal R, ∃ m' : M, x • m' = a • m := by
    intro a ha
    have h := hm₀ a ha
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    exact ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h).imp fun m' hm' => hm'.2
  obtain ⟨a, ha⟩ := key y₁ hy₁
  obtain ⟨b, hb⟩ := key y₂ hy₂

  have hab : y₂ • a = y₁ • b := by
    apply hxreg
    show x • y₂ • a = x • y₁ • b
    rw [smul_comm x y₂ a, ha, smul_comm y₂ y₁ m, ← hb, smul_comm y₁ x b]

  have ha0 : (Submodule.Quotient.mk a : QuotSMulTop y₁ M) = 0 := by
    apply hy₂reg
    show y₂ • (Submodule.Quotient.mk a : QuotSMulTop y₁ M) = y₂ • (0 : QuotSMulTop y₁ M)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hab, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨b, Submodule.mem_top, rfl⟩
  rw [Submodule.Quotient.mk_eq_zero] at ha0
  obtain ⟨c, -, hc⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp ha0

  have hm : m = x • c := by
    apply hy₁reg
    show y₁ • m = y₁ • (x • c)
    rw [← ha, ← hc, smul_comm x y₁ c]
  rw [hm]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨c, Submodule.mem_top, rfl⟩

end Elementary
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section AssociatedPrimes

variable [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma not_isAssociatedPrime_maximalIdeal_of_isSMulRegular {x : R}
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ¬ IsAssociatedPrime (maximalIdeal R) M := by
  intro h
  obtain ⟨hp, y, hyy⟩ := isAssociatedPrime_iff.mp h

  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [hyy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem ⊥
  apply hy0
  apply hxreg
  show x • y = x • (0 : M)
  rw [smul_zero]
  have hxy : x ∈ (⊥ : Submodule R M).colon {y} := hyy ▸ hx
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at hxy

variable (M) in

lemma not_isAssociatedPrime_maximalIdeal_quotSMulTop {x : R} (hxreg : IsSMulRegular M x)
    (hdepth : (2 : ℕ∞) ≤ Module.depth R M) :
    ¬ IsAssociatedPrime (maximalIdeal R) (QuotSMulTop x M) := by

  obtain ⟨pr, hpr, hpr', hprlen⟩ :=
    exists_isWeaklyRegular_of_le_depth M 2 (by exact_mod_cast hdepth)
  obtain ⟨y₁, y₂, rfl⟩ : ∃ y₁ y₂, pr = [y₁, y₂] := by
    rcases pr with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, t⟩⟩⟩ <;>
      first
        | exact ⟨_, _, rfl⟩
        | (exfalso; simp only [List.length_nil, List.length_cons] at hprlen; omega)
  intro h
  obtain ⟨hp, y, hyy⟩ := isAssociatedPrime_iff.mp h
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hp.ne_top
    rw [hyy, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem ⊥
  apply hy0
  apply eq_zero_of_maximalIdeal_smul_eq_zero hxreg hpr (hpr' y₁ (by simp)) (hpr' y₂ (by simp))
  intro a ha
  have hay : a ∈ (⊥ : Submodule R (QuotSMulTop x M)).colon {y} := hyy ▸ ha
  rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at hay

lemma exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
    (N₁ N₂ : Type*) [AddCommGroup N₁] [Module R N₁] [Module.Finite R N₁]
    [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₂]
    (h₁ : ¬ IsAssociatedPrime (maximalIdeal R) N₁)
    (h₂ : ¬ IsAssociatedPrime (maximalIdeal R) N₂) :
    ∃ z ∈ maximalIdeal R, IsSMulRegular N₁ z ∧ IsSMulRegular N₂ z := by
  by_contra hcon

  have hsub : (maximalIdeal R : Set R) ⊆
      ⋃ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂ : Set (Ideal R)), (p : Set R) := by
    intro z hz
    rw [Set.biUnion_union]
    by_cases hreg : IsSMulRegular N₁ z
    · refine Set.mem_union_right _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₂]
      exact fun hreg2 => hcon ⟨z, hz, hreg, hreg2⟩
    · refine Set.mem_union_left _ ?_
      rw [biUnion_associatedPrimes_eq_compl_regular R N₁]
      exact hreg
  have hfin : (associatedPrimes R N₁ ∪ associatedPrimes R N₂).Finite :=
    (associatedPrimes.finite R N₁).union (associatedPrimes.finite R N₂)
  have hprime : ∀ p ∈ (associatedPrimes R N₁ ∪ associatedPrimes R N₂),
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) - -
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hpmem, hple⟩ := (Ideal.subset_union_prime_finite hfin (f := id)
    (I := maximalIdeal R) ⊥ ⊥ hprime).mp (by simpa using hsub)

  have hpprime : p.IsPrime := by
    rcases hpmem with hp | hp
    · exact hp.isPrime
    · exact hp.isPrime
  have hpeq : p = maximalIdeal R := le_antisymm (le_maximalIdeal hpprime.ne_top) hple
  rw [hpeq] at hpmem
  rcases hpmem with hp | hp
  · exact h₁ hp
  · exact h₂ hp

end AssociatedPrimes
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section DepthDrop

variable [IsNoetherianRing R]

lemma depth_quotSMulTop_succ_le (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 ≤ Module.depth R M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [Module.depth_of_subsingleton R (QuotSMulTop x M), Module.depth_of_subsingleton R M,
      top_add]
  · have hQ : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    have hlt : Module.depth R (QuotSMulTop x M) < ⊤ := depth_lt_top (QuotSMulTop x M)
    cases hd : Module.depth R (QuotSMulTop x M) with
    | top => exact absurd hd hlt.ne
    | coe n =>
      obtain ⟨s, hs, hs', hlen⟩ :=
        exists_isWeaklyRegular_of_le_depth (QuotSMulTop x M) n (le_of_eq hd.symm)
      have hcons : Sequence.IsWeaklyRegular M (x :: s) :=
        (Sequence.isWeaklyRegular_cons_iff M x s).mpr ⟨hxreg, hs⟩
      have hmem : ∀ r ∈ x :: s, r ∈ maximalIdeal R := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hx
        · exact hs' r hr
      have hle := Module.length_le_depth R M (x :: s) hcons hmem
      rw [List.length_cons, hlen] at hle
      exact_mod_cast hle

lemma le_depth_quotSMulTop_of_succ_le_depth
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (n : ℕ) (hxreg : IsSMulRegular M x)
    (hd : ((n + 1 : ℕ) : ℕ∞) ≤ Module.depth R M) :
    (n : ℕ∞) ≤ Module.depth R (QuotSMulTop x M) := by
  induction n generalizing M with
  | zero => simp
  | succ n IH =>
    rcases subsingleton_or_nontrivial M with hM | hM
    · rw [Module.depth_of_subsingleton R (QuotSMulTop x M)]
      exact le_top
    ·
      have hAssQ : ¬ IsAssociatedPrime (maximalIdeal R) (QuotSMulTop x M) :=
        not_isAssociatedPrime_maximalIdeal_quotSMulTop M hxreg
          (le_trans (by exact_mod_cast Nat.cast_le.mpr (by omega : 2 ≤ n + 1 + 1)) hd)

      obtain ⟨s, hs, hs', hlen⟩ := exists_isWeaklyRegular_of_le_depth M (n + 1 + 1) hd
      have hsne : s ≠ [] := by
        intro h
        rw [h, List.length_nil] at hlen
        omega
      obtain ⟨s', w, rfl, hs'len⟩ : ∃ s' w, s = s' ++ [w] ∧ s'.length = n + 1 := by
        refine ⟨s.dropLast, s.getLast hsne, (List.dropLast_append_getLast hsne).symm, ?_⟩
        rw [List.length_dropLast, hlen]
        omega
      have hsplit := (Sequence.isWeaklyRegular_append_iff M s' [w]).mp hs
      have hwreg : IsSMulRegular (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) w :=
        (Sequence.isWeaklyRegular_singleton_iff _ w).mp hsplit.2
      have hwm : w ∈ maximalIdeal R := hs' w (by simp)

      have hAssN : ¬ IsAssociatedPrime (maximalIdeal R)
          (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) :=
        not_isAssociatedPrime_maximalIdeal_of_isSMulRegular hwm hwreg

      obtain ⟨z, hz, hzregQ, hzregN⟩ := exists_mem_maximalIdeal_isSMulRegular_isSMulRegular
        (QuotSMulTop x M) (M ⧸ (Ideal.ofList s' • ⊤ : Submodule R M)) hAssQ hAssN

      have hs'z : Sequence.IsWeaklyRegular M (s' ++ [z]) :=
        (Sequence.isWeaklyRegular_append_iff M s' [z]).mpr
          ⟨hsplit.1, (Sequence.isWeaklyRegular_singleton_iff _ z).mpr hzregN⟩
      have hs'mem : ∀ r ∈ s', r ∈ maximalIdeal R :=
        fun r hr => hs' r (List.mem_append_left _ hr)
      have hzs' : Sequence.IsWeaklyRegular M (z :: s') := by
        apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hs'z
          (List.perm_append_singleton z s')
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact hs'mem r hr
        · rw [List.mem_singleton] at hr
          subst hr
          exact hz

      have hs'Mz : Sequence.IsWeaklyRegular (QuotSMulTop z M) s' :=
        ((Sequence.isWeaklyRegular_cons_iff M z s').mp hzs').2
      have hdMz : ((n + 1 : ℕ) : ℕ∞) ≤ Module.depth R (QuotSMulTop z M) := by
        have hle := Module.length_le_depth R (QuotSMulTop z M) s' hs'Mz hs'mem
        rwa [hs'len] at hle

      have hxz : Sequence.IsWeaklyRegular M [x, z] :=
        (Sequence.isWeaklyRegular_cons_iff M x [z]).mpr
          ⟨hxreg, (Sequence.isWeaklyRegular_singleton_iff _ z).mpr hzregQ⟩
      have hzx : Sequence.IsWeaklyRegular M [z, x] := by
        apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hxz
          (List.Perm.swap z x [])
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx
        · exact hz
      have hxregMz : IsSMulRegular (QuotSMulTop z M) x :=
        (Sequence.isWeaklyRegular_singleton_iff _ x).mp
          ((Sequence.isWeaklyRegular_cons_iff M z [x]).mp hzx).2

      have hIH : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop x (QuotSMulTop z M)) :=
        IH (QuotSMulTop z M) hxregMz hdMz
      rw [depth_eq_of_linearEquiv (quotSMulTopQuotSMulTopComm M x z)] at hIH

      obtain ⟨t, ht, ht', htlen⟩ :=
        exists_isWeaklyRegular_of_le_depth (QuotSMulTop z (QuotSMulTop x M)) n hIH
      have hfinal : Sequence.IsWeaklyRegular (QuotSMulTop x M) (z :: t) :=
        (Sequence.isWeaklyRegular_cons_iff _ z t).mpr ⟨hzregQ, ht⟩
      have hmemzt : ∀ r ∈ z :: t, r ∈ maximalIdeal R := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hz
        · exact ht' r hr
      have hle := Module.length_le_depth R (QuotSMulTop x M) (z :: t) hfinal hmemzt
      rw [List.length_cons, htlen] at hle
      exact_mod_cast hle

variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem depth_quotSMulTop_succ_eq {x : R} (hx : x ∈ maximalIdeal R)
    (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 = Module.depth R M := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · rw [Module.depth_of_subsingleton R (QuotSMulTop x M), Module.depth_of_subsingleton R M,
      top_add]
  · refine le_antisymm (depth_quotSMulTop_succ_le M hx hxreg) ?_
    have hMlt : Module.depth R M < ⊤ := depth_lt_top M
    cases hdM : Module.depth R M with
    | top => exact absurd hdM hMlt.ne
    | coe d =>

      have hxmem : ∀ r ∈ [x], r ∈ maximalIdeal R := by
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        exact hx
      have hd1 : 1 ≤ d := by
        have hle := Module.length_le_depth R M [x]
          ((Sequence.isWeaklyRegular_singleton_iff M x).mpr hxreg) hxmem
        rw [hdM] at hle
        exact_mod_cast hle

      have hd2 : ((d - 1 + 1 : ℕ) : ℕ∞) ≤ Module.depth R M := by
        rw [hdM]
        exact Nat.cast_le.mpr (by omega : d - 1 + 1 ≤ d)
      have hhard := le_depth_quotSMulTop_of_succ_le_depth M hx (d - 1) hxreg hd2
      calc ((d : ℕ) : ℕ∞) = ((d - 1 : ℕ) : ℕ∞) + 1 := by
            rw [show ((d - 1 : ℕ) : ℕ∞) + 1 = ((d - 1 + 1 : ℕ) : ℕ∞) by push_cast; ring]
            congr 1
            omega
        _ ≤ Module.depth R (QuotSMulTop x M) + 1 := add_le_add hhard le_rfl

theorem depth_quotSMulTop_eq_sub_one {x : R} (hx : x ∈ maximalIdeal R)
    (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) = Module.depth R M - 1 := by
  rw [← depth_quotSMulTop_succ_eq M hx hxreg]
  exact ((ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right).symm

end DepthDrop
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section QuotientCurrency

lemma exists_mem_maximalIdeal_mk_eq {I : Ideal R} [IsLocalRing (R ⧸ I)]
    (a : R ⧸ I) (ha : a ∈ maximalIdeal (R ⧸ I)) :
    ∃ y ∈ maximalIdeal R, Ideal.Quotient.mk I y = a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨y, ?_, rfl⟩
  intro hy
  exact ha (hy.map (Ideal.Quotient.mk I))

theorem depth_quotient_eq_depth (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N := by
  have hloc : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

  have hcomp : (algebraMap R (R ⧸ I)) ∘
      (Function.surjInv (Ideal.Quotient.mk_surjective (I := I))) = id := by
    funext a
    rw [Function.comp_apply, Ideal.Quotient.algebraMap_eq,
      Function.surjInv_eq Ideal.Quotient.mk_surjective a, id_eq]
  apply le_antisymm
  ·
    refine sSup_le_sSup ?_
    rintro b ⟨t, ht, ht', rfl⟩
    refine ⟨t.map (Function.surjInv Ideal.Quotient.mk_surjective), ?_, ?_, by
      rw [List.length_map]⟩
    ·
      have hmap : (t.map (Function.surjInv Ideal.Quotient.mk_surjective)).map
          (algebraMap R (R ⧸ I)) = t := by
        rw [List.map_map, hcomp, List.map_id]
      rw [← Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) N, hmap]
      exact ht
    ·
      intro r hr
      rw [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      intro hu
      apply ht' a ha
      rw [← Function.surjInv_eq Ideal.Quotient.mk_surjective a]
      exact hu.map (Ideal.Quotient.mk I)
  ·
    refine sSup_le_sSup ?_
    rintro b ⟨s, hs, hs', rfl⟩
    refine ⟨s.map (Ideal.Quotient.mk I), ?_, ?_, by rw [List.length_map]⟩
    · have hmk : s.map (Ideal.Quotient.mk I) = s.map (algebraMap R (R ⧸ I)) := by
        rw [Ideal.Quotient.algebraMap_eq]
      rw [hmk, Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ I) N]
      exact hs
    · intro r hr
      rw [List.mem_map] at hr
      obtain ⟨a, ha, rfl⟩ := hr
      intro hu
      exact hs' a ha (hloc.map_nonunit a hu)

lemma isLocalRing_quotient_span_singleton {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    rw [Ideal.span_singleton_eq_top] at h
    exact hx h
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

variable [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem depth_quotient_quotSMulTop_succ_eq {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x M) + 1 = Module.depth R M := by
  rw [depth_quotient_eq_depth (Ideal.span {x}) (QuotSMulTop x M)]
  exact depth_quotSMulTop_succ_eq M hx hxreg

theorem depth_quotient_quotSMulTop_eq_sub_one {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.depth R M - 1 := by
  rw [← depth_quotient_quotSMulTop_succ_eq M hx hxreg]
  exact ((ENat.addLECancellable_of_ne_top ENat.one_ne_top).add_tsub_cancel_right).symm

theorem depth_quotient_self_succ_eq {x : R} [IsLocalRing (R ⧸ Ideal.span {x})]
    (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular R x) :
    Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x R) + 1 = Module.depth R R :=
  depth_quotient_quotSMulTop_succ_eq R hx hxreg

end QuotientCurrency
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section KrullDim

variable (R) [IsNoetherianRing R]

theorem ringKrullDim_quotient_span_singleton_succ {x : R}
    (hxreg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hx

theorem ringKrullDim_quotient_span_singleton_succ_of_ne_zero [IsDomain R] {x : R}
    (hx0 : x ≠ 0) (hx : x ∈ maximalIdeal R) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hx0) hx

theorem ringKrullDim_quotient_span_singleton_succ_of_regular_parameter [IsDomain R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ (maximalIdeal R) ^ 2) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
  ringKrullDim_quotient_span_singleton_succ_of_ne_zero R
    (fun h => hx2 (h ▸ zero_mem ((maximalIdeal R) ^ 2))) hx

theorem ringKrullDim_eq_succ_of_quotient_span_singleton_eq {x : R}
    (hxreg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) {d : ℕ}
    (hd : ringKrullDim (R ⧸ Ideal.span {x}) = ((d : ℕ) : WithBot ℕ∞)) :
    ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞) := by
  rw [← ringKrullDim_quotient_span_singleton_succ R hxreg hx, hd]
  exact (Nat.cast_add_one (R := WithBot ℕ∞) d).symm

theorem ringKrullDim_quotient_span_singleton_of_ringKrullDim_eq {x : R}
    (hxreg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) {d : ℕ}
    (hd : ringKrullDim R = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ Ideal.span {x}) = ((d : ℕ) : WithBot ℕ∞) := by
  have h := ringKrullDim_quotient_span_singleton_succ R hxreg hx
  rw [hd] at h

  haveI : IsLocalRing (R ⧸ Ideal.span {x}) := isLocalRing_quotient_span_singleton hx
  have hbot : ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim (R ⧸ Ideal.span {x}) ≠ ⊤ := ringKrullDim_ne_top
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (R ⧸ Ideal.span {x}) = ((m : ℕ) : WithBot ℕ∞) := by
    cases hk : ringKrullDim (R ⧸ Ideal.span {x}) with
    | bot => exact absurd hk hbot
    | coe e =>
      cases e with
      | top => exact absurd hk htop
      | coe m => exact ⟨m, by norm_cast⟩
  rw [hm] at h ⊢

  rw [← Nat.cast_add_one (R := WithBot ℕ∞) m] at h
  have hmd : m + 1 = d + 1 := by exact_mod_cast h
  have hfin : m = d := by omega
  rw [hfin]

end KrullDim
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end Module
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section SATGates

variable (K : Type) [Field K]

example : Module.depth (PowerSeries K) (QuotSMulTop (PowerSeries.X : PowerSeries K)
      (PowerSeries K)) + 1 = Module.depth (PowerSeries K) (PowerSeries K) :=
  Module.depth_quotSMulTop_succ_eq (PowerSeries K)
    PowerSeries.X_mem_maximalIdeal PowerSeries.isSMulRegular_X

example : ringKrullDim ((PowerSeries K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)}) + 1 =
      ringKrullDim (PowerSeries K) :=
  Module.ringKrullDim_quotient_span_singleton_succ (PowerSeries K)
    PowerSeries.isSMulRegular_X PowerSeries.X_mem_maximalIdeal

local instance : IsLocalRing ((PowerSeries K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)}) :=
  Module.isLocalRing_quotient_span_singleton (PowerSeries.X_mem_maximalIdeal (R := K))

example : Module.depth ((PowerSeries K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries K)})
      (QuotSMulTop (PowerSeries.X : PowerSeries K) (PowerSeries K)) + 1 =
      Module.depth (PowerSeries K) (PowerSeries K) :=
  Module.depth_quotient_quotSMulTop_succ_eq (PowerSeries K)
    PowerSeries.X_mem_maximalIdeal PowerSeries.isSMulRegular_X

end SATGates
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section

p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"

section Characterization

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

lemma Module.exists_isSMulRegular_of_notMem_associatedPrimes
    (h : maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  have h' : ¬ IsAssociatedPrime (maximalIdeal R) M := fun hip =>
    h (AssociatedPrimes.mem_iff.mpr hip)
  obtain ⟨z, hz, hreg, -⟩ :=
    Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular M M h' h'
  exact ⟨z, hz, hreg⟩

lemma Module.depth_pos_of_maximalIdeal_notMem_associatedPrimes
    (h : maximalIdeal R ∉ associatedPrimes R M) : 0 < Module.depth R M := by
  obtain ⟨x, hx, hreg⟩ := Module.exists_isSMulRegular_of_notMem_associatedPrimes R M h
  exact Module.depth_pos_of_isSMulRegular R M hx hreg

theorem Module.depth_pos_iff_maximalIdeal_notMem_associatedPrimes :
    0 < Module.depth R M ↔ maximalIdeal R ∉ associatedPrimes R M :=
  ⟨Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos R M,
   Module.depth_pos_of_maximalIdeal_notMem_associatedPrimes R M⟩

theorem Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes :
    Module.depth R M = 0 ↔ maximalIdeal R ∈ associatedPrimes R M := by
  constructor
  · intro h0
    by_contra hnot
    exact absurd h0
      (Module.depth_pos_of_maximalIdeal_notMem_associatedPrimes R M hnot).ne'
  · intro hmem
    by_contra hne
    have hpos : 0 < Module.depth R M :=
      zero_lt_one.trans_le (ENat.one_le_iff_ne_zero.mpr hne)
    exact Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos R M hpos hmem

theorem Module.depth_pos_iff_not_isAssociatedPrime_maximalIdeal :
    0 < Module.depth R M ↔ ¬ IsAssociatedPrime (maximalIdeal R) M := by
  constructor
  · intro h hip
    exact (Module.depth_pos_iff_maximalIdeal_notMem_associatedPrimes R M).mp h
      (AssociatedPrimes.mem_iff.mpr hip)
  · intro h
    exact (Module.depth_pos_iff_maximalIdeal_notMem_associatedPrimes R M).mpr
      fun hmem => h (AssociatedPrimes.mem_iff.mp hmem)

theorem Module.depth_eq_zero_iff_isAssociatedPrime_maximalIdeal :
    Module.depth R M = 0 ↔ IsAssociatedPrime (maximalIdeal R) M := by
  constructor
  · intro h0
    exact AssociatedPrimes.mem_iff.mp
      ((Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes R M).mp h0)
  · intro hip
    exact (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes R M).mpr
      (AssociatedPrimes.mem_iff.mpr hip)

end Characterization
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Degeneration

variable (R : Type*) [CommRing R] [IsLocalRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

theorem Module.depth_eq_top_and_associatedPrimes_eq_empty_of_subsingleton [Subsingleton M] :
    Module.depth R M = ⊤ ∧ associatedPrimes R M = ∅ :=
  ⟨Module.depth_of_subsingleton R M, associatedPrimes.eq_empty_of_subsingleton⟩

theorem Module.depth_pos_and_maximalIdeal_notMem_associatedPrimes_of_subsingleton
    [Subsingleton M] :
    0 < Module.depth R M ∧ maximalIdeal R ∉ associatedPrimes R M := by
  constructor
  · rw [Module.depth_of_subsingleton R M]
    exact zero_lt_one.trans_le le_top
  · rw [associatedPrimes.eq_empty_of_subsingleton]
    exact Set.notMem_empty _

end Degeneration
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

namespace DepthZeroAssociatedPrime
open DepthZeroAssociatedPrime

theorem gate_dvr_maximalIdeal_notMem_associatedPrimes
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] :
    maximalIdeal 𝓞 ∉ associatedPrimes 𝓞 𝓞 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝓞
  have hπm : π ∈ maximalIdeal 𝓞 := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span rfl
  have hπreg : IsSMulRegular 𝓞 π := by
    intro a b hab
    exact mul_left_cancel₀ hπ.ne_zero (by simpa only [smul_eq_mul] using hab)
  intro hmem
  exact Module.not_isAssociatedPrime_maximalIdeal_of_isSMulRegular hπm hπreg
    (AssociatedPrimes.mem_iff.mp hmem)

theorem gate_dvr_depth_pos
    (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] :
    0 < Module.depth 𝓞 𝓞 :=
  (Module.depth_pos_iff_maximalIdeal_notMem_associatedPrimes 𝓞 𝓞).mpr
    (gate_dvr_maximalIdeal_notMem_associatedPrimes 𝓞)

example (𝓞 : Type*) [CommRing 𝓞] [IsDomain 𝓞] [IsDiscreteValuationRing 𝓞] :
    Module.depth 𝓞 𝓞 = 1 := by
  exact_mod_cast (IsLocalRing.IsCohenMacaulayOfDim.of_isDiscreteValuationRing 𝓞).depth_eq

theorem gate_field_maximalIdeal_mem_associatedPrimes (K : Type*) [Field K] :
    maximalIdeal K ∈ associatedPrimes K K := by
  rw [IsLocalRing.maximalIdeal_eq_bot, AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine ⟨Ideal.isPrime_bot, 1, ?_⟩
  ext r
  rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_one]

theorem gate_field_depth_eq_zero (K : Type*) [Field K] : Module.depth K K = 0 :=
  (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes K K).mpr
    (gate_field_maximalIdeal_mem_associatedPrimes K)

example (K : Type*) [Field K] : Module.depth K K = 0 := by
  exact_mod_cast (IsLocalRing.IsCohenMacaulayOfDim.of_field K).depth_eq

theorem gate_field_maximalIdeal_mem_associatedPrimes_via_depth (K : Type*) [Field K] :
    maximalIdeal K ∈ associatedPrimes K K :=
  (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes K K).mp
    (by exact_mod_cast (IsLocalRing.IsCohenMacaulayOfDim.of_field K).depth_eq)

theorem gate_rat_depth_eq_zero_and_mem :
    Module.depth ℚ ℚ = 0 ∧ maximalIdeal ℚ ∈ associatedPrimes ℚ ℚ :=
  ⟨gate_field_depth_eq_zero ℚ, gate_field_maximalIdeal_mem_associatedPrimes ℚ⟩

end DepthZeroAssociatedPrime
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section

p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory Pointwise"

noncomputable section

section DimensionDrop

variable {R : Type*} [CommRing R]

lemma ringKrullDim_quotient_succ_le_of_lt {p q : Ideal R} [p.IsPrime] (hpq : p < q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  obtain ⟨x, hxq, hxp⟩ := SetLike.exists_of_lt hpq
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq.le)
    (Ideal.Quotient.factor_surjective hpq.le) (r := Ideal.Quotient.mk p x) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero
      fun h => hxp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hxq

end DimensionDrop
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section PTorsionScaffolding

variable {R : Type*} [CommRing R]

private def pTorsion (p : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R M where
  carrier := {m : M | ∀ a ∈ p, a • m = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := by
    intro m₁ m₂ h₁ h₂
    show ∀ a ∈ p, a • (m₁ + m₂) = 0
    intro a ha
    rw [smul_add, h₁ a ha, h₂ a ha, add_zero]
  smul_mem' := by
    intro c m hm
    show ∀ a ∈ p, a • (c • m) = 0
    intro a ha
    rw [smul_comm, hm a ha, smul_zero]

end PTorsionScaffolding
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section NakayamaStep

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma IsAssociatedPrime.exists_forall_smul_eq_zero_notMem_smul_top
    [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ k : M, (∀ a ∈ p, a • k = 0) ∧ k ∉ x • (⊤ : Submodule R M) := by

  obtain ⟨hp_prime, z, hz⟩ := isAssociatedPrime_iff.mp hp
  have hz0 : z ≠ 0 := by
    rintro rfl
    refine hp_prime.ne_top ?_
    rw [hz, Submodule.colon_singleton_zero]
  have hzann : ∀ a ∈ p, a • z = 0 := by
    intro a ha
    have haz : a ∈ (⊥ : Submodule R M).colon {z} := hz ▸ ha
    rwa [Submodule.mem_colon_singleton, Submodule.mem_bot] at haz

  by_contra hcon
  have hcon' : ∀ k : M, (∀ a ∈ p, a • k = 0) → k ∈ x • (⊤ : Submodule R M) := by
    intro k hk
    by_contra hknot
    exact hcon ⟨k, hk, hknot⟩

  have hKle : pTorsion p M ≤ x • (⊤ : Submodule R M) := by
    intro k hk
    have hk' : ∀ a ∈ p, a • k = 0 := hk
    exact hcon' k hk'

  have hKxK : pTorsion p M ≤ Ideal.span {x} • pTorsion p M := by
    rw [Submodule.ideal_span_singleton_smul]
    intro k hk
    have hk' : ∀ a ∈ p, a • k = 0 := hk
    obtain ⟨m, -, hm⟩ := (Submodule.mem_smul_pointwise_iff_exists k x ⊤).mp (hKle hk)
    have hmK : ∀ a ∈ p, a • m = 0 := by
      intro a ha
      apply hxreg
      show x • a • m = x • (0 : M)
      rw [smul_zero, smul_comm x a m, hm]
      exact hk' a ha
    have hmK' : m ∈ pTorsion p M := hmK
    exact (Submodule.mem_smul_pointwise_iff_exists k x (pTorsion p M)).mpr ⟨m, hmK', hm⟩

  have hKbot : pTorsion p M = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) (pTorsion p M)
      (IsNoetherian.noetherian (pTorsion p M)) hKxK ?_
    refine le_trans ?_ (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx

  have hzK : z ∈ pTorsion p M := hzann
  rw [hKbot, Submodule.mem_bot] at hzK
  exact hz0 hzK

lemma IsAssociatedPrime.exists_isAssociatedPrime_quotSMulTop_le
    [Module.Finite R M] {p : Ideal R} (hp : IsAssociatedPrime p M)
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    ∃ q : Ideal R, IsAssociatedPrime q (QuotSMulTop x M) ∧ p ≤ q ∧ x ∈ q := by
  obtain ⟨k, hkp, hkx⟩ := (Ws14Port.IsAssociatedPrime.exists_forall_smul_eq_zero_notMem_smul_top hp) hx hxreg

  have hk0 : (Submodule.Quotient.mk k : QuotSMulTop x M) ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero]
    exact hkx

  obtain ⟨q, hq, hle⟩ :=
    exists_le_isAssociatedPrime_of_isNoetherianRing R (Submodule.Quotient.mk k) hk0
  refine ⟨q, hq, ?_, ?_⟩
  ·
    intro a ha
    refine hle ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      hkp a ha, Submodule.Quotient.mk_eq_zero]
    exact Submodule.zero_mem _
  ·
    refine hle ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul k x ⊤ Submodule.mem_top

end NakayamaStep
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section MainTheorem

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private lemma depth_le_ringKrullDim_quotient_aux (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R),
      IsAssociatedPrime p M → (n : ℕ∞) ≤ Module.depth R M →
      ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  induction n with
  | zero =>
    intro M _ _ _ p hp _
    have hprime : p.IsPrime := hp.isPrime
    have hnt : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
    simpa using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p)
  | succ n IH =>
    intro M _ _ _ p hp hn
    have hprime : p.IsPrime := hp.isPrime

    have hpos : 0 < Module.depth R M := by
      refine lt_of_lt_of_le ?_ hn
      exact_mod_cast Nat.succ_pos n
    obtain ⟨x, hx, hxreg⟩ := Module.exists_isSMulRegular_of_depth_pos R M hpos

    have hpSet : p ∈ associatedPrimes R M := hp
    have hxp : x ∉ p := by
      intro hxpmem
      have hmem : x ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
        Set.mem_biUnion hpSet hxpmem
      rw [biUnion_associatedPrimes_eq_compl_regular R M] at hmem
      exact hmem hxreg

    obtain ⟨q, hq, hpq, hxq⟩ := (Ws14Port.IsAssociatedPrime.exists_isAssociatedPrime_quotSMulTop_le hp) hx hxreg

    have hdrop : (n : ℕ∞) ≤ Module.depth R (QuotSMulTop x M) :=
      Module.le_depth_quotSMulTop_of_succ_le_depth M hx n hxreg (by exact_mod_cast hn)

    have hIH : ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) :=
      IH (QuotSMulTop x M) q hq hdrop

    have hlt : p < q := lt_of_le_of_ne hpq (by rintro rfl; exact hxp hxq)
    have hdim : ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
      ringKrullDim_quotient_succ_le_of_lt hlt

    push_cast
    calc ((n : ℕ) : WithBot ℕ∞) + 1
        ≤ ringKrullDim (R ⧸ q) + 1 := add_le_add hIH le_rfl
      _ ≤ ringKrullDim (R ⧸ p) := hdim

lemma Module.natCast_le_ringKrullDim_quotient_of_le_depth (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M)
    (hn : (n : ℕ∞) ≤ Module.depth R M) :
    ((n : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) :=
  depth_le_ringKrullDim_quotient_aux n M p hp hn

theorem Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ p) := by
  have hp' : IsAssociatedPrime p M := hp

  have hM : Nontrivial M := by
    rcases subsingleton_or_nontrivial M with hsub | hnt
    · exact absurd hp' not_isAssociatedPrime_of_subsingleton
    · exact hnt

  have hlt : Module.depth R M < ⊤ := Module.depth_lt_top M
  cases hd : Module.depth R M with
  | top => exact absurd hd hlt.ne
  | coe d =>

    exact Module.natCast_le_ringKrullDim_quotient_of_le_depth d M hp (le_of_eq hd.symm)

theorem Module.depth_le_ringKrullDim_quotient_of_isAssociatedPrime
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : IsAssociatedPrime p M) :
    .some (Module.depth R M) ≤ ringKrullDim (R ⧸ p) :=
  Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes M hp

end MainTheorem
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Unmixedness

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace IsLocalRing
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing"

namespace IsCohenMacaulayOfDim
open IsCohenMacaulayOfDim

theorem ringKrullDim_quotient_eq_of_mem_associatedPrimes {d : ℕ}
    (hCM : IsCohenMacaulayOfDim R d) {p : Ideal R}
    (hp : p ∈ associatedPrimes R R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  refine le_antisymm (ringKrullDim_quotient_le p) ?_
  have h1 := Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes R hp
  rw [hCM.depth_eq] at h1
  rw [hCM.ringKrullDim_eq]
  exact h1

theorem mem_minimalPrimes_of_mem_associatedPrimes {d : ℕ}
    (hCM : IsCohenMacaulayOfDim R d) {p : Ideal R}
    (hp : p ∈ associatedPrimes R R) :
    p ∈ minimalPrimes R := by
  have hp' : IsAssociatedPrime p R := hp
  have hprime : p.IsPrime := hp'.isPrime
  rw [minimalPrimes_eq_minimals]
  refine ⟨hprime, ?_⟩
  intro q hq hqp

  by_contra hpq
  have hlt : q < p := lt_of_le_of_ne hqp fun h => hpq (le_of_eq h.symm)

  have hdrop : ringKrullDim (R ⧸ p) + 1 ≤ ringKrullDim (R ⧸ q) :=
    ringKrullDim_quotient_succ_le_of_lt hlt

  rw [hCM.ringKrullDim_quotient_eq_of_mem_associatedPrimes hp, hCM.ringKrullDim_eq] at hdrop
  have hub : ringKrullDim (R ⧸ q) ≤ ringKrullDim R := ringKrullDim_quotient_le q
  rw [hCM.ringKrullDim_eq] at hub
  have hcontra : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ ((d : ℕ) : WithBot ℕ∞) := hdrop.trans hub
  exact absurd (ENat.WithBot.add_one_le_iff.mp hcontra) (lt_irrefl _)

end IsCohenMacaulayOfDim
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

lemma isCohenMacaulayOfDim_of_depth_eq_ringKrullDim
    (h : .some (Module.depth R R) = ringKrullDim R) :
    ∃ d : ℕ, IsCohenMacaulayOfDim R d := by
  have hlt : Module.depth R R < ⊤ := Module.depth_lt_top R
  cases hd : Module.depth R R with
  | top => exact absurd hd hlt.ne
  | coe d =>
    refine ⟨d, ?_, ?_⟩
    · rw [← h, hd]
      rfl
    · exact_mod_cast hd

theorem mem_minimalPrimes_of_mem_associatedPrimes_of_depth_eq_ringKrullDim
    (h : .some (Module.depth R R) = ringKrullDim R)
    {p : Ideal R} (hp : p ∈ associatedPrimes R R) :
    p ∈ minimalPrimes R := by
  obtain ⟨d, hCM⟩ := isCohenMacaulayOfDim_of_depth_eq_ringKrullDim h
  exact hCM.mem_minimalPrimes_of_mem_associatedPrimes hp

end IsLocalRing
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end Unmixedness
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Gates

variable (K : Type) [Field K]

example :
    (⊥ : Ideal K) ∈ associatedPrimes K K ∧
      .some (Module.depth K K) ≤ ringKrullDim (K ⧸ (⊥ : Ideal K)) ∧
      (⊥ : Ideal K) ∈ minimalPrimes K := by
  have hbot : (⊥ : Ideal K) ∈ associatedPrimes K K := by
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    refine ⟨Ideal.isPrime_bot, 1, ?_⟩
    ext r
    rw [Submodule.mem_colon_singleton, smul_eq_mul, mul_one]
  refine ⟨hbot, ?_, ?_⟩
  · exact Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes K hbot
  · exact (IsLocalRing.IsCohenMacaulayOfDim.of_field K).mem_minimalPrimes_of_mem_associatedPrimes
      hbot

example :
    ∃ p ∈ associatedPrimes (PowerSeries K) (PowerSeries K),
      .some (Module.depth (PowerSeries K) (PowerSeries K)) ≤
        ringKrullDim (PowerSeries K ⧸ p) := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (PowerSeries K) (PowerSeries K)
  exact ⟨p, hp,
    Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes (PowerSeries K) hp⟩

example {p : Ideal (PowerSeries K)}
    (hp : p ∈ associatedPrimes (PowerSeries K) (PowerSeries K)) :
    p ∈ minimalPrimes (PowerSeries K) :=
  (PowerSeries.isCohenMacaulayOfDim_succ K
    (IsLocalRing.IsCohenMacaulayOfDim.of_field K)).mem_minimalPrimes_of_mem_associatedPrimes hp

end Gates
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing Submodule P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.Module Function"
open scoped Pointwise
noncomputable section
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

namespace QuotSMulTop
open QuotSMulTop

section Bookkeeping

variable (x : R)

@[scoped simp]
theorem mk_smul_mk (r : R) (m : M) :
    (Ideal.Quotient.mk (Ideal.span {x}) r) •
        (Submodule.Quotient.mk m : QuotSMulTop x M) =
      (Submodule.Quotient.mk (r • m) : QuotSMulTop x M) :=
  rfl

theorem quotientMk_smul (r : R) (q : QuotSMulTop x M) :
    (Ideal.Quotient.mk (Ideal.span {x}) r) • q = r • q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rfl

scoped instance instModuleFiniteQuotient [Module.Finite R M] :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Finite.of_restrictScalars_finite R _ _

theorem nontrivial_quotientRing [IsLocalRing R] (hx : x ∈ maximalIdeal R) :
    Nontrivial (R ⧸ Ideal.span {x}) :=
  Ideal.Quotient.nontrivial_iff.mpr fun h =>
    (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp
        (h ▸ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx) :
          Ideal.span {x} ≤ maximalIdeal R)))

theorem span_le_jacobson_bot [IsLocalRing R] (hx : x ∈ maximalIdeal R) :
    Ideal.span {x} ≤ Ideal.jacobson ⊥ :=
  le_trans (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)

end Bookkeeping
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section RankOne

variable (x : R)

theorem free_self : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x R) := by

  set f : (R ⧸ Ideal.span {x}) →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x R :=
    LinearMap.toSpanSingleton (R ⧸ Ideal.span {x}) (QuotSMulTop x R)
      (Submodule.Quotient.mk (1 : R)) with hf_def

  have hf_apply : ∀ r : R,
      f (Ideal.Quotient.mk (Ideal.span {x}) r) = (Submodule.Quotient.mk r : QuotSMulTop x R) := by
    intro r
    rw [hf_def, LinearMap.toSpanSingleton_apply, mk_smul_mk, smul_eq_mul, mul_one]

  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hf_apply, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨a, -, rfl⟩ := hc
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨a, rfl⟩

  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Ideal.Quotient.mk _ r, hf_apply r⟩
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end RankOne
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Engines

variable [IsLocalRing R] (x : R)

theorem span_eq_top_of_span_quotientMk_eq_top [Module.Finite R M]
    (hx : x ∈ maximalIdeal R) {ι : Type*} (m : ι → M)
    (hspan : Submodule.span (R ⧸ Ideal.span {x})
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤) :
    Submodule.span R (Set.range m) = ⊤ := by

  have h1 : Submodule.span R
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [← Submodule.restrictScalars_span R (R ⧸ Ideal.span {x}) Ideal.Quotient.mk_surjective,
      hspan, Submodule.restrictScalars_top]

  have h2 : (Submodule.span R (Set.range m)).map
      (Submodule.mkQ (x • ⊤ : Submodule R M)) = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact h1

  rw [Submodule.map_mkQ_eq_top] at h2
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (span_le_jacobson_bot x hx) ?_)
  rw [Submodule.ideal_span_singleton_smul, sup_comm, h2]

theorem linearIndependent_of_quotientMk_linearIndependent [IsNoetherianRing R]
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) {ι : Type*} [Fintype ι] (m : ι → M)
    (hli : LinearIndependent (R ⧸ Ideal.span {x})
      (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M))) :
    LinearIndependent R m := by
  classical

  have hker_le : LinearMap.ker (Fintype.linearCombination R m) ≤
      Ideal.span {x} • LinearMap.ker (Fintype.linearCombination R m) := by
    intro a ha
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha

    have hcoeff : ∀ i, Ideal.Quotient.mk (Ideal.span {x}) (a i) = 0 := by
      have h0 : ∑ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
          (Submodule.Quotient.mk (m i) : QuotSMulTop x M) = 0 := by
        have hterm : ∀ i, (Ideal.Quotient.mk (Ideal.span {x}) (a i)) •
            (Submodule.Quotient.mk (m i) : QuotSMulTop x M)
            = (Submodule.mkQ (x • ⊤ : Submodule R M)) (a i • m i) := fun i => rfl
        simp_rw [hterm, ← map_sum, ha, map_zero]
      exact Fintype.linearIndependent_iff.mp hli _ h0

    have hdvd : ∀ i, x ∣ a i := fun i =>
      Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (hcoeff i))
    choose c hc using hdvd
    have ha_eq : a = x • c := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact hc i

    have hc_ker : c ∈ LinearMap.ker (Fintype.linearCombination R m) := by
      rw [LinearMap.mem_ker]
      apply hreg
      show x • Fintype.linearCombination R m c = x • (0 : M)
      rw [smul_zero, ← map_smul, ← ha_eq]
      exact ha

    rw [ha_eq]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hc_ker

  have hker : LinearMap.ker (Fintype.linearCombination R m) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _
      (IsNoetherian.noetherian _) hker_le (span_le_jacobson_bot x hx)

  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg_ker : g ∈ LinearMap.ker (Fintype.linearCombination R m) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    exact hg
  rw [hker, Submodule.mem_bot] at hg_ker
  exact congrFun hg_ker i

end Engines
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

section Main

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] (x : R)

theorem exists_basis_lift (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    {ι : Type*} [Fintype ι]
    (b : Module.Basis ι (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    ∃ b' : Module.Basis ι R M,
      ∀ i, (Submodule.Quotient.mk (b' i) : QuotSMulTop x M) = b i := by

  choose m hm using fun i =>
    Submodule.Quotient.mk_surjective (x • ⊤ : Submodule R M) (b i)

  have hmk_eq : (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⇑b := funext hm

  have hli : LinearIndependent (R ⧸ Ideal.span {x})
      (fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) := by
    rw [hmk_eq]; exact b.linearIndependent
  have hspan : Submodule.span (R ⧸ Ideal.span {x})
      (Set.range fun i => (Submodule.Quotient.mk (m i) : QuotSMulTop x M)) = ⊤ := by
    rw [hmk_eq]; exact b.span_eq

  have hli' : LinearIndependent R m :=
    linearIndependent_of_quotientMk_linearIndependent x hx hreg m hli
  have hspan' : Submodule.span R (Set.range m) = ⊤ :=
    span_eq_top_of_span_quotientMk_eq_top x hx m hspan

  refine ⟨Module.Basis.mk hli' hspan'.ge, fun i => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hm i

end Main
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries"

end QuotSMulTop
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section MainTheorems

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

theorem Module.free_of_quotSMulTop_free (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x)
    (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Free R M := by
  haveI := hfree

  haveI : Fintype (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
    Module.Free.ChooseBasisIndex.fintype _ _
  obtain ⟨b', -⟩ := QuotSMulTop.exists_basis_lift x hx hreg
    (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
  exact Module.Free.of_basis b'

theorem Module.free_of_quotSMulTop_free_of_regular_param (x : R)
    (hx : x ∈ IsLocalRing.maximalIdeal R) (_hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2)
    (_hregR : IsSMulRegular R x) (hregM : IsSMulRegular M x)
    (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Free R M :=
  Module.free_of_quotSMulTop_free x hx hregM hfree

theorem Module.finrank_quotSMulTop_eq (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M x)
    (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.finrank (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = Module.finrank R M := by
  haveI := hfree
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := QuotSMulTop.nontrivial_quotientRing x hx
  haveI : Fintype (Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :=
    Module.Free.ChooseBasisIndex.fintype _ _
  obtain ⟨b', -⟩ := QuotSMulTop.exists_basis_lift x hx hreg
    (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
  rw [Module.finrank_eq_card_basis b',
    Module.finrank_eq_card_basis
      (Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M))]

end MainTheorems
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"
open scoped Pointwise

namespace No4PatchingCore
open No4PatchingCore

section QuotientInfrastructure

variable {R : Type u} [CommRing R]

private theorem _root_.Ws14Port.No4PatchingCore.isLocalRing_quotient_span_singleton [IsLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) : IsLocalRing (R ⧸ Ideal.span {x}) := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)))
  haveI : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

p2m_export "Ws14Port.No4PatchingCore" "isLocalRing_quotient_span_singleton"

theorem isScalarTower_quotient_span_singleton {M : Type v} [AddCommGroup M] [Module R M]
    (x : R) : IsScalarTower R (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl

theorem moduleFinite_quotient_span_singleton {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  haveI := isScalarTower_quotient_span_singleton (R := R) (M := M) x
  exact Module.Finite.of_restrictScalars_finite R _ _

theorem nontrivial_quotSMulTop_of_mem_maximalIdeal [IsLocalRing R] {M : Type v}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) : Nontrivial (QuotSMulTop x M) := by
  apply Submodule.Quotient.nontrivial_iff.2
  rw [← Submodule.ideal_span_singleton_smul, ne_comm]
  apply Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
  refine le_trans ?_ (maximalIdeal_le_jacobson _)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact hx

theorem exists_ringKrullDim_eq_natCast (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have h1 : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  have h2 : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  cases hd : ringKrullDim R with
  | bot => exact absurd hd h2
  | coe d =>
    cases d with
    | top => exact absurd hd (by simpa using h1)
    | coe d => exact ⟨d, rfl⟩

end QuotientInfrastructure
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section BaseCase

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

theorem isField_of_spanFinrank_maximalIdeal_eq_zero
    (hn : (maximalIdeal R).spanFinrank = 0) : IsField R :=
  IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      ((maximalIdeal R).fg_of_isNoetherianRing)).mp hn)

variable (M : Type v) [AddCommGroup M] [Module R M]

theorem free_of_spanFinrank_maximalIdeal_eq_zero
    (hn : (maximalIdeal R).spanFinrank = 0) : Module.Free R M := by
  letI : Field R := (isField_of_spanFinrank_maximalIdeal_eq_zero R hn).toField
  exact Module.Free.of_divisionRing R M

theorem free_of_ringKrullDim_eq_zero (hdim : ringKrullDim R = 0) : Module.Free R M := by
  apply free_of_spanFinrank_maximalIdeal_eq_zero R M
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hdim] at h
  exact_mod_cast h

end BaseCase
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section Exchange

variable (R : Type u) [CommRing R]

theorem exists_finite_span_eq_maximalIdeal_mem [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ S : Set R, x ∈ S ∧ S.Finite ∧ S.ncard ≤ (maximalIdeal R).spanFinrank ∧
      Ideal.span S = maximalIdeal R := by
  classical

  set ξ : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩ with hξdef
  have hξ0 : ξ ≠ 0 := by
    rw [hξdef, ne_eq, Ideal.toCotangent_eq_zero]
    exact hx2

  have hli : LinearIndepOn (ResidueField R) id ({ξ} : Set (CotangentSpace R)) := by
    refine LinearIndepOn.singleton' ?_
    intro r hr
    rcases smul_eq_zero.mp hr with h | h
    · exact h
    · exact absurd h hξ0

  obtain ⟨B, hξB, hBfin, hBcard, hBspan⟩ :
      ∃ B : Set (CotangentSpace R), ξ ∈ B ∧ B.Finite ∧
        B.ncard = (maximalIdeal R).spanFinrank ∧
        Submodule.span (ResidueField R) B = ⊤ := by
    refine ⟨hli.extend (Set.subset_univ _),
      hli.subset_extend _ (Set.mem_singleton ξ), ?_, ?_, ?_⟩
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      exact Set.toFinite _
    · haveI : Finite (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Module.Finite.finite_basis (Module.Basis.extend hli)
      haveI : Fintype (hli.extend (Set.subset_univ ({ξ} : Set (CotangentSpace R)))) :=
        Fintype.ofFinite _
      rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R,
        Module.finrank_eq_card_basis (Module.Basis.extend hli),
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    · have h1 := (Module.Basis.extend hli).span_eq
      rwa [Module.Basis.range_extend] at h1

  choose lift hlift using (maximalIdeal R).toCotangent_surjective
  set S₀ : Set ↥(maximalIdeal R) := insert ⟨x, hx⟩ (lift '' (B \ {ξ})) with hS₀def

  have himg : (maximalIdeal R).toCotangent '' S₀ = B := by
    rw [hS₀def, Set.image_insert_eq, ← hξdef, ← Set.image_comp]
    have hcomp : ((maximalIdeal R).toCotangent ∘ lift) '' (B \ {ξ}) = B \ {ξ} := by
      have : ∀ v ∈ B \ {ξ}, ((maximalIdeal R).toCotangent ∘ lift) v = id v :=
        fun v _ => hlift v
      rw [Set.image_congr this, Set.image_id]
    rw [hcomp, Set.insert_diff_singleton, Set.insert_eq_self.mpr hξB]

  have hspanR : Submodule.span R S₀ = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [himg, hBspan]
  have hspan : Ideal.span ((↑) '' S₀ : Set R) = maximalIdeal R := by
    have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspanR
    rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype] at hmap

  refine ⟨(↑) '' S₀, ⟨⟨x, hx⟩, by rw [hS₀def]; exact Set.mem_insert _ _, rfl⟩, ?_, ?_, hspan⟩
  · rw [hS₀def]
    exact (((hBfin.diff).image _).insert _).image _
  ·
    have hfin₁ : (lift '' (B \ {ξ})).Finite := (hBfin.diff).image _
    have h1 : ((↑) '' S₀ : Set R).ncard ≤ S₀.ncard := by
      apply Set.ncard_image_le
      rw [hS₀def]; exact hfin₁.insert _
    have h2 : S₀.ncard ≤ (lift '' (B \ {ξ})).ncard + 1 := by
      rw [hS₀def]; exact Set.ncard_insert_le _ _
    have h3 : (lift '' (B \ {ξ})).ncard ≤ (B \ {ξ}).ncard :=
      Set.ncard_image_le hBfin.diff
    have h4 : (B \ {ξ}).ncard + 1 = B.ncard :=
      Set.ncard_diff_singleton_add_one hξB hBfin
    omega

variable [IsRegularLocalRing R]

theorem isRegularLocalRing_quotient_span_singleton
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxreg : IsSMulRegular R x) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by

  obtain ⟨S, hxS, hSfin, hScard, hSspan⟩ :=
    exists_finite_span_eq_maximalIdeal_mem R hx hx2

  have hmax' : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmkx : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (S \ {x})) := by
    rw [← hSspan, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        rw [SetLike.mem_coe, hmkx]
        exact Submodule.zero_mem _
      · exact Ideal.subset_span ⟨y, ⟨hy, hyx⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono Set.diff_subset)

  have hsf_le : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
    have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ (S \ {x}).ncard := by
      rw [← hmax', hmap]
      exact le_trans
        (Submodule.spanFinrank_span_le_ncard_of_finite ((hSfin.diff).image _))
        (Set.ncard_image_le hSfin.diff)
    have h2 : (S \ {x}).ncard + 1 = S.ncard :=
      Set.ncard_diff_singleton_add_one hxS hSfin
    omega

  have hkrull : ringKrullDim (R ⧸ Ideal.span {x}) ≤
      ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have hdrop : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hxreg hx
  have hregR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal

  have hsqueeze : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcalc : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hregR, ← hdrop]
      calc ringKrullDim (R ⧸ Ideal.span {x}) + 1
          ≤ ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 :=
            add_le_add hkrull le_rfl
        _ = (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
            push_cast
            ring
    exact_mod_cast hcalc
  have hkey : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
      (maximalIdeal R).spanFinrank := by omega

  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
  have hd1 : (d : ℕ) + 1 = (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) =
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      have h5 : ringKrullDim (R ⧸ Ideal.span {x}) + 1 =
          (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdrop, ← hregR]
        exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ∞) hkey.symm
      rw [hd] at h5
      rw [← h5]
      push_cast
      ring
    exact_mod_cast hcast
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, hkey⟩
  rw [hd]
  have : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = d := by omega
  exact_mod_cast this.le

end Exchange
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section Carriers

def JointRegularElementSelection : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    0 < Module.depth R M → 0 < ringKrullDim R →
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x ∧ IsSMulRegular M x

def DepthDropQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ maximalIdeal R → IsSMulRegular R x → IsSMulRegular M x →
    ∀ [IsLocalRing (R ⧸ Ideal.span {x})],
    Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x M) + 1 = Module.depth R M

def QuotientInductionStep : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ maximalIdeal R → x ∉ maximalIdeal R ^ 2 →
    IsSMulRegular R x → IsSMulRegular M x →
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) →
    Module.Free R M

end Carriers
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section Assembly

theorem free_of_depth_eq_ringKrullDim_aux
    (hsel : JointRegularElementSelection.{u, v})
    (hdrop : DepthDropQuotient.{u, v})
    (hstep : QuotientInductionStep.{u, v}) :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
      (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
      (maximalIdeal R).spanFinrank = n →
      .some (Module.depth R M) = ringKrullDim R → Module.Free R M := by
  intro n
  induction n with
  | zero =>

    intro R _ _ M _ _ _ hn _
    exact free_of_spanFinrank_maximalIdeal_eq_zero R M hn
  | succ n IH =>
    intro R _ _ M _ _ _ hn H

    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]

    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Module.Free.of_subsingleton R M

    have hdepth : Module.depth R M = ((n + 1 : ℕ) : ℕ∞) := by
      have h1 : (.some (Module.depth R M) : WithBot ℕ∞) = ((n + 1 : ℕ) : WithBot ℕ∞) :=
        H.trans hdim
      exact_mod_cast h1
    have hdepth_pos : 0 < Module.depth R M := by
      rw [hdepth]
      exact_mod_cast Nat.succ_pos n
    have hdim_pos : 0 < ringKrullDim R := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos n

    obtain ⟨x, hx_mem, hx_sq, hxR, hxM⟩ := hsel R M hdepth_pos hdim_pos

    haveI hloc : IsLocalRing (R ⧸ Ideal.span {x}) :=
      isLocalRing_quotient_span_singleton hx_mem
    haveI : IsScalarTower R (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      isScalarTower_quotient_span_singleton x
    haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      moduleFinite_quotient_span_singleton x

    obtain ⟨hreg', hsf'⟩ := isRegularLocalRing_quotient_span_singleton R hx_mem hx_sq hxR
    haveI := hreg'
    have hsf'n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      rw [hn] at hsf'
      omega

    have hdd := hdrop R M x hx_mem hxR hxM
    have hdepth' : Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x M) = (n : ℕ∞) := by
      rw [hdepth] at hdd
      have hcast : ((n + 1 : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast] at hdd
      exact WithTop.add_right_cancel (by simp : (1 : ℕ∞) ≠ ⊤) hdd

    have hH' : (.some (Module.depth (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) : WithBot ℕ∞) =
        ringKrullDim (R ⧸ Ideal.span {x}) := by
      rw [hdepth', ← IsRegularLocalRing.spanFinrank_maximalIdeal
        (R := R ⧸ Ideal.span {x}), hsf'n]
      rfl
    have hfree' : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
      IH (R ⧸ Ideal.span {x}) (QuotSMulTop x M) hsf'n hH'

    exact hstep R M x hx_mem hx_sq hxR hxM hfree'

theorem free_of_depth_eq_ringKrullDim
    (hsel : JointRegularElementSelection.{u, v})
    (hdrop : DepthDropQuotient.{u, v})
    (hstep : QuotientInductionStep.{u, v})
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : .some (Module.depth R M) = ringKrullDim R) : Module.Free R M :=
  free_of_depth_eq_ringKrullDim_aux hsel hdrop hstep
    ((maximalIdeal R).spanFinrank) R M rfl H

theorem free_of_depth_eq_ringKrullDim_of_dim_zero
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (hdim : ringKrullDim R = 0) : Module.Free R M :=
  free_of_ringKrullDim_eq_zero R M hdim

end Assembly
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section SiblingWiring

theorem quotientInductionStep_holds : QuotientInductionStep.{u, v} := by
  intro R _ _ _ M _ _ _ _ x hx hx2 hxR hxM hfree
  exact Module.free_of_quotSMulTop_free_of_regular_param x hx hx2 hxR hxM hfree

def RegularPositiveDepth : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    0 < ringKrullDim R → 0 < Module.depth R R

theorem jointRegularElementSelection_of_regularPositiveDepth
    (hbridge : RegularPositiveDepth.{u}) : JointRegularElementSelection.{u, v} := by
  intro R _ _ M _ _ _ _ hdepthM hdim
  exact Module.exists_isSMulRegular_and_isSMulRegular_of_depth_pos R M
    (hbridge R hdim) hdepthM

theorem free_of_depth_eq_ringKrullDim_of_landed_siblings
    (hbridge : RegularPositiveDepth.{u})
    (hdrop : DepthDropQuotient.{u, v})
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : .some (Module.depth R M) = ringKrullDim R) : Module.Free R M :=
  free_of_depth_eq_ringKrullDim
    (jointRegularElementSelection_of_regularPositiveDepth hbridge)
    hdrop quotientInductionStep_holds R M H

end SiblingWiring
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end No4PatchingCore
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"

namespace No4PatchingCore
open No4PatchingCore

theorem depthDropQuotient_holds : DepthDropQuotient.{u, v} := by
  intro R _ _ _ M _ _ _ _ x hx _hxR hxM _
  exact Module.depth_quotient_quotSMulTop_succ_eq M hx hxM

end No4PatchingCore
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section
p2m_open "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.IsLocalRing Module.IsLocalRing P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.RingTheory"
open scoped Pointwise

namespace No4PatchingCore
open No4PatchingCore

section PrimeAvoidance

theorem maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos
    (R : Type u) [CommRing R] [IsLocalRing R] (hdim : 0 < ringKrullDim R) :
    maximalIdeal R ∉ minimalPrimes R := by
  intro hmem

  have hall : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := fun p =>
    le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      (hmem.2 ⟨p.isPrime, bot_le⟩ (IsLocalRing.le_maximalIdeal p.isPrime.ne_top))
  haveI : Subsingleton (PrimeSpectrum R) :=
    ⟨fun p q => PrimeSpectrum.ext ((hall p).trans (hall q).symm)⟩
  have heq : ringKrullDim R = 0 := by
    rw [ringKrullDim]
    haveI : Nonempty (PrimeSpectrum R) := ⟨⟨maximalIdeal R, inferInstance⟩⟩
    letI : Unique (PrimeSpectrum R) := uniqueOfSubsingleton (Classical.arbitrary _)
    exact Order.krullDim_eq_zero_of_unique
  rw [heq] at hdim
  exact hdim.false

theorem exists_parameter_notMem_minimalPrimes
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : 0 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  have hbot : maximalIdeal R ≠ ⊥ :=
    IsLocalRing.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim

  have hfin : (insert ((maximalIdeal R) ^ 2) (minimalPrimes R)).Finite :=
    Set.Finite.insert _ (minimalPrimes.finite_of_isNoetherianRing R)

  have hnotle : ¬ ∃ I ∈ hfin.toFinset, maximalIdeal R ≤ I := by
    rintro ⟨I, hIs, hle⟩
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    ·
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
        (maximalIdeal R) (IsNoetherian.noetherian _) ?_
        (IsLocalRing.maximalIdeal_le_jacobson _))
      rwa [Ideal.smul_eq_mul, ← pow_two]
    ·
      have hp_prime : I.IsPrime := Ideal.minimalPrimes_isPrime hI
      have heq : I = maximalIdeal R :=
        (IsLocalRing.le_maximalIdeal hp_prime.ne_top).antisymm hle
      rw [heq] at hI
      exact maximalIdeal_notMem_minimalPrimes_of_ringKrullDim_pos R hdim hI

  have havoid : ¬ ((maximalIdeal R : Set R) ⊆
      ⋃ I ∈ (hfin.toFinset : Set (Ideal R)), (I : Set R)) := by
    intro hsub
    refine hnotle ((Ideal.subset_union_prime (s := hfin.toFinset) (f := fun I => I)
      ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2) ?_).mp hsub)
    intro I hIs hI₁ _
    rw [Set.Finite.mem_toFinset, Set.mem_insert_iff] at hIs
    rcases hIs with rfl | hI
    · exact absurd rfl hI₁
    · exact Ideal.minimalPrimes_isPrime hI

  rw [hfin.coe_toFinset] at havoid
  obtain ⟨x, hxm, hxout⟩ := Set.not_subset.mp havoid
  refine ⟨x, hxm, ?_, ?_⟩
  ·
    intro hx2
    exact hxout (Set.mem_biUnion (Set.mem_insert _ _) hx2)
  ·
    intro p hp hxp
    exact hxout (Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp)

end PrimeAvoidance
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section DimensionDrop

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

theorem annihilator_self_eq_bot (R : Type u) [CommRing R] : Module.annihilator R R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  simpa using Module.mem_annihilator.mp hr 1

theorem ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R := by
  rw [← Module.supportDim_quotient_eq_ringKrullDim, ← Module.supportDim_self_eq_ringKrullDim]
  refine Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    ?_ hx
  intro p hp
  refine hxmin p ?_
  rwa [annihilator_self_eq_bot] at hp

theorem ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) :
    ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R := by
  have hkey : ringKrullDim (QuotSMulTop x R) + 1 = ringKrullDim R :=
    ringKrullDim_quotSMulTop_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hspan : Ideal.span {x} = x • (⊤ : Ideal R) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq R hspan).toRingEquiv]
  exact hkey

end DimensionDrop
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section QuotientRegularity

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

theorem isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
        (maximalIdeal R).spanFinrank := by

  obtain ⟨S, hxS, hSfin, hScard, hSspan⟩ :=
    exists_finite_span_eq_maximalIdeal_mem R hx hx2

  have hmax' : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmkx : (Ideal.Quotient.mk (Ideal.span {x})) x = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) =
      Ideal.span ((Ideal.Quotient.mk (Ideal.span {x})) '' (S \ {x})) := by
    rw [← hSspan, Ideal.map_span]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨y, hy, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        rw [SetLike.mem_coe, hmkx]
        exact Submodule.zero_mem _
      · exact Ideal.subset_span ⟨y, ⟨hy, hyx⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono Set.diff_subset)

  have hsf_le : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤
      (maximalIdeal R).spanFinrank := by
    have h1 : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank ≤ (S \ {x}).ncard := by
      rw [← hmax', hmap]
      exact le_trans
        (Submodule.spanFinrank_span_le_ncard_of_finite ((hSfin.diff).image _))
        (Set.ncard_image_le hSfin.diff)
    have h2 : (S \ {x}).ncard + 1 = S.ncard :=
      Set.ncard_diff_singleton_add_one hxS hSfin
    omega

  have hkrull : ringKrullDim (R ⧸ Ideal.span {x}) ≤
      ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal _
  have hdrop : ringKrullDim (R ⧸ Ideal.span {x}) + 1 = ringKrullDim R :=
    ringKrullDim_quotient_span_singleton_succ_eq_of_forall_notMem_minimalPrimes hx hxmin
  have hregR : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)

  have hsqueeze : (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcalc : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      rw [hregR, ← hdrop]
      calc ringKrullDim (R ⧸ Ideal.span {x}) + 1
          ≤ ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 :=
            add_le_add hkrull le_rfl
        _ = (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
            push_cast
            ring
    exact_mod_cast hcalc
  have hkey : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 =
      (maximalIdeal R).spanFinrank := by omega

  obtain ⟨d, hd⟩ := exists_ringKrullDim_eq_natCast (R ⧸ Ideal.span {x})
  have hd1 : (d : ℕ) + 1 = (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
    have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) =
        (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
      have h5 : ringKrullDim (R ⧸ Ideal.span {x}) + 1 =
          (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        rw [hdrop, ← hregR]
        exact_mod_cast congrArg (Nat.cast : ℕ → WithBot ℕ∞) hkey.symm
      rw [hd] at h5
      rw [← h5]
      push_cast
      ring
    exact_mod_cast hcast
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_, hkey⟩
  rw [hd]
  have : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = d := by omega
  exact_mod_cast this.le

end QuotientRegularity
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section MatsumuraDomain

theorem isDomain_of_isRegularLocalRing_aux :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = n → IsDomain R := by
  intro n
  induction n with
  | zero =>

    intro R _ _ hn
    have hbot : maximalIdeal R = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot
        ((maximalIdeal R).fg_of_isNoetherianRing)).mp hn
    haveI hprime : (⊥ : Ideal R).IsPrime := hbot ▸ (maximalIdeal.isMaximal R).isPrime
    exact IsDomain.of_bot_isPrime R
  | succ n IH =>
    intro R _ _ hn

    have hdim : ringKrullDim R = ((n + 1 : ℕ) : WithBot ℕ∞) := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
    have hdim_pos : 0 < ringKrullDim R := by
      rw [hdim]
      exact_mod_cast Nat.succ_pos n

    obtain ⟨x, hx_mem, hx_sq, hx_min⟩ := exists_parameter_notMem_minimalPrimes R hdim_pos

    haveI hloc : IsLocalRing (R ⧸ Ideal.span {x}) :=
      isLocalRing_quotient_span_singleton hx_mem
    obtain ⟨hreg', hsf'⟩ :=
      isRegularLocalRing_quotient_span_singleton_of_forall_notMem_minimalPrimes R
        hx_mem hx_sq hx_min
    haveI := hreg'
    have hsf'n : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = n := by
      rw [hn] at hsf'
      omega

    have hdom' : IsDomain (R ⧸ Ideal.span {x}) := IH (R ⧸ Ideal.span {x}) hsf'n
    have hprime : (Ideal.span {x}).IsPrime := by
      rw [← Ideal.Quotient.isDomain_iff_prime]
      exact hdom'

    haveI := hprime
    obtain ⟨p, hp_min, hp_le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := Ideal.span {x}) bot_le
    have hp_prime : p.IsPrime := Ideal.minimalPrimes_isPrime hp_min
    have hxp : x ∉ p := hx_min p hp_min

    have hple : p ≤ (maximalIdeal R) • p := by
      intro a ha
      obtain ⟨r, hrx⟩ := Ideal.mem_span_singleton'.mp (hp_le ha)
      have hrp : r ∈ p := by
        have hmem : r * x ∈ p := by rw [hrx]; exact ha
        rcases hp_prime.mem_or_mem hmem with h | h
        · exact h
        · exact absurd h hxp
      rw [Ideal.smul_eq_mul, ← hrx, mul_comm r x]
      exact Ideal.mul_mem_mul hx_mem hrp

    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p) hple (IsLocalRing.maximalIdeal_le_jacobson _)

    haveI : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    exact IsDomain.of_bot_isPrime R

theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux ((maximalIdeal R).spanFinrank) R rfl

end MatsumuraDomain
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section PositiveDepth

theorem depth_self_pos_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : 0 < ringKrullDim R) : 0 < Module.depth R R := by
  haveI : IsDomain R := isDomain_of_isRegularLocalRing R
  obtain ⟨y, hym, hy0⟩ := (Submodule.ne_bot_iff _).mp
    (IsLocalRing.maximalIdeal_ne_bot_of_ringKrullDim_pos R hdim)
  refine Module.depth_pos_of_isSMulRegular R R hym ?_
  intro a b hab
  exact mul_left_cancel₀ hy0 (by simpa only [smul_eq_mul] using hab)

theorem regularPositiveDepth_holds : RegularPositiveDepth.{u} := by
  intro R _ _ hdim
  exact depth_self_pos_of_isRegularLocalRing R hdim

end PositiveDepth
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

section Unconditional

theorem jointRegularElementSelection_holds : JointRegularElementSelection.{u, v} :=
  jointRegularElementSelection_of_regularPositiveDepth regularPositiveDepth_holds.{u}

theorem free_of_depth_eq_ringKrullDim_unconditional
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : .some (Module.depth R M) = ringKrullDim R) : Module.Free R M :=
  free_of_depth_eq_ringKrullDim_of_landed_siblings regularPositiveDepth_holds.{u}
    depthDropQuotient_holds.{u, v} R M H

end Unconditional
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end No4PatchingCore
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop"

end Ws14Port
p2m_reactivate "P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.PowerSeries P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port.QuotSMulTop P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.Ws14Port"

theorem solution
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : (Module.depth R M : WithBot ℕ∞) = ringKrullDim R) : Module.Free R M :=
  Ws14Port.No4PatchingCore.free_of_depth_eq_ringKrullDim_unconditional R M H

end S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
end P2MW
export P2MW.S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing (solution)
