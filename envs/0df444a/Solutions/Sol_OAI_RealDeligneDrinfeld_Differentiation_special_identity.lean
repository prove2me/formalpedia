-- Prove2me | solution 1 for OAI.RealDeligneDrinfeld.Differentiation.special_identity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:53:56.726975+00:00
-- url     : https://prove2.me/submissions/ce572d6b-46e0-4969-b068-321bba83a7a4

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid

set_option linter.all false










section

namespace OAI

noncomputable section
namespace RealDeligneDrinfeld

namespace AssociativeModel

variable {α : Type*}
abbrev FL (α : Type*) := FreeLieAlgebra ℝ α
abbrev A (α : Type*) := MonoidAlgebra ℝ (FreeMonoid α)
attribute [local instance] LieRing.ofAssociativeRing

def atom (a : α) : A α := MonoidAlgebra.single (FreeMonoid.of a) 1

def embed : FL α →ₗ⁅ℝ⁆ A α := FreeLieAlgebra.lift ℝ atom

@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of ℝ a) = atom a := by
  simp [embed]

def dynkinWord : List α → FL α
  | [] => 0
  | [a] => FreeLieAlgebra.of ℝ a
  | a :: b :: w => ⁅FreeLieAlgebra.of ℝ a, dynkinWord (b :: w)⁆

theorem dynkinWord_cons (a : α) (w : List α) (hw : w ≠ []) :
    dynkinWord (a::w) = ⁅FreeLieAlgebra.of ℝ a, dynkinWord w⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => rfl

def wordLinear {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : FreeMonoid α → M) : A α →ₗ[ℝ] M :=
  (Finsupp.linearCombination ℝ f).comp (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp] theorem wordLinear_single {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : FreeMonoid α → M) (w : FreeMonoid α) (c : ℝ) :
    wordLinear f (MonoidAlgebra.single w c) = c • f w := by
  change Finsupp.linearCombination ℝ f (Finsupp.single w c) = _; simp

def dynkin : A α →ₗ[ℝ] FL α := wordLinear (fun w => dynkinWord w.toList)

def wordAct : FreeMonoid α →* Module.End ℝ (FL α) :=
  FreeMonoid.lift (fun a => LieAlgebra.ad ℝ (FL α) (FreeLieAlgebra.of ℝ a))

def act : A α →ₐ[ℝ] Module.End ℝ (FL α) :=
  MonoidAlgebra.lift ℝ (Module.End ℝ (FL α)) (FreeMonoid α) wordAct

@[simp] theorem act_single (w : FreeMonoid α) (c : ℝ) :
    act (MonoidAlgebra.single w c) = c • wordAct w := by simp [act]

@[simp] theorem wordAct_of_apply (a : α) (q : FL α) :
    wordAct (FreeMonoid.of a) q = ⁅FreeLieAlgebra.of ℝ a,q⁆ := by
  simp [wordAct, LieAlgebra.ad_apply]

@[simp] theorem act_embed (p q : FL α) : act (embed p) q = ⁅p,q⁆ := by
  have h : act.toLieHom.comp embed = LieAlgebra.ad ℝ (FL α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [atom, wordAct]
  exact LinearMap.congr_fun (LieHom.congr_fun h p) q

theorem dynkinWord_append (u v : List α) (hv : v ≠ []) :
    dynkinWord (u++v) = wordAct (FreeMonoid.ofList u) (dynkinWord v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, dynkinWord_cons _ _ (List.append_ne_nil_of_right_ne_nil u hv),
      ih, FreeMonoid.ofList_cons, map_mul, Module.End.mul_apply, wordAct_of_apply]

def homogeneous (n : ℕ) : Submodule ℝ (A α) :=
  Submodule.span ℝ {p | ∃ w : FreeMonoid α,
    w.toList.length = n ∧ p = MonoidAlgebra.single w 1}

theorem single_mem_homogeneous (w : FreeMonoid α) (n : ℕ)
    (hn : w.toList.length = n) : MonoidAlgebra.single w 1 ∈ homogeneous (α := α) n :=
  Submodule.subset_span ⟨w, hn, rfl⟩

theorem mul_homogeneous {n m : ℕ} {a b : A α}
    (ha : a ∈ homogeneous n) (hb : b ∈ homogeneous m) : a*b ∈ homogeneous (n+m) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨v,hv,rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      simpa only [MonoidAlgebra.single_mul_single, one_mul] using
        single_mem_homogeneous (v*w) (n+m) (by simp [hv,hw])
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (homogeneous (n+m)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (homogeneous (n+m)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (homogeneous (n+m)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (homogeneous (n+m)).smul_mem r ha

theorem dynkin_mul {n : ℕ} (hn : n > 0) (a : A α) {b : A α}
    (hb : b ∈ homogeneous n) : dynkin (a*b) = act a (dynkin b) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp [add_mul, ha, hc]
  | single v r =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      have hw' : w.toList ≠ [] := by intro h; simp [h] at hw; omega
      simp [dynkin, dynkinWord_append _ _ hw']
    | zero => simp
    | add b c _ _ hb hc => simp [mul_add, hb, hc]
    | smul r b _ hb => simp [hb]

theorem dynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    0 < n ∧ embed p ∈ homogeneous n ∧ dynkin (embed p) = (n : ℝ) • p := by
  induction hp with
  | generator a =>
    refine ⟨by omega, ?_, ?_⟩
    · simpa [atom] using single_mem_homogeneous (FreeMonoid.of a) 1 rfl
    · simp [dynkin, atom, dynkinWord]
  | @bracket n m p q hp hq ihp ihq =>
    rcases ihp with ⟨hn,hn',hpn⟩
    rcases ihq with ⟨hm,hm',hqm⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [LieHom.map_lie]
      change embed p * embed q - embed q * embed p ∈ homogeneous (n+m)
      exact (homogeneous (n+m)).sub_mem (mul_homogeneous hn' hm')
        (by simpa [Nat.add_comm] using mul_homogeneous hm' hn')
    · rw [LieHom.map_lie]
      change dynkin (embed p * embed q - embed q * embed p) = _
      rw [map_sub, dynkin_mul hm _ hm', dynkin_mul hn _ hn', hqm, hpn]
      simp only [map_smul, act_embed]
      rw [← lie_skew q p]
      simp only [smul_neg, sub_neg_eq_add, Nat.cast_add, add_smul]
      exact add_comm _ _

def normalizedDynkin : A α →ₗ[ℝ] FL α :=
  wordLinear (fun w => (w.toList.length : ℝ)⁻¹ • dynkinWord w.toList)

theorem normalizedDynkin_homogeneous {n : ℕ} {a : A α}
    (ha : a ∈ homogeneous n) : normalizedDynkin a = (n : ℝ)⁻¹ • dynkin a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w,hw,rfl⟩
    simp [normalizedDynkin, dynkin, hw]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, smul_add]
  | smul r a _ ha =>
    rw [map_smul, map_smul, ha, smul_comm]

theorem normalizedDynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) : normalizedDynkin (embed p) = p := by
  obtain ⟨hn,hn',hp'⟩ := dynkin_embed_word hp
  rw [normalizedDynkin_homogeneous hn', hp', smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt hn)

theorem mem_word_span (wt : α → ℕ) (p : FL α) :
    p ∈ Submodule.span ℝ {q | ∃ n, WeightedWord wt n q} := by
  let S : Submodule ℝ (FL α) := Submodule.span ℝ {q | ∃ n, WeightedWord wt n q}
  change p ∈ S
  induction p using freeLie_induction with
  | h0 => exact S.zero_mem
  | hg a => exact Submodule.subset_span ⟨wt a, WeightedWord.generator a⟩
  | ha a b ha hb => exact S.add_mem ha hb
  | hs r a ha => exact S.smul_mem r ha
  | hl a b ha hb =>
    induction ha using Submodule.span_induction with
    | mem a ha =>
      rcases ha with ⟨n, hn⟩
      induction hb using Submodule.span_induction with
      | mem b hb =>
        rcases hb with ⟨m, hm⟩
        exact Submodule.subset_span ⟨n+m, WeightedWord.bracket hn hm⟩
      | zero => simp
      | add b c _ _ hb hc => simpa only [lie_add] using S.add_mem hb hc
      | smul r b _ hb => simpa only [lie_smul] using S.smul_mem r hb
    | zero => simp
    | add a c _ _ ha hc => simpa only [add_lie] using S.add_mem ha hc
    | smul r a _ ha => simpa only [smul_lie] using S.smul_mem r ha

theorem normalizedDynkin_embed (p : FL α) : normalizedDynkin (embed p) = p := by
  have hp := mem_word_span (fun _ : α => 1) p
  induction hp using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,hn⟩ := ha
    exact normalizedDynkin_embed_word hn
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]

end AssociativeModel

namespace FreeDerivations

variable {R : Type*} [CommRing R]
variable {M : Type*} [LieRing M] [LieAlgebra R M]

structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M

def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩

@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all

@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl

instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]

def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl

variable {α : Type*}
local notation "F" => FreeLieAlgebra R α

def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)

@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p

def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]

variable [DecidableEq α]
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)

@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]

@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]

@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]

end FreeDerivations

namespace AssociativeModel
attribute [local instance] LieRing.ofAssociativeRing
variable {α : Type*}

theorem coeff_rotate {P : A α} {b : α} (h : atom b * P = P * atom b) (w : List α) :
    P.coeff (FreeMonoid.ofList (b :: w)) = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
  calc
    P.coeff (FreeMonoid.ofList (b :: w)) =
        (P * atom b).coeff ((FreeMonoid.of b * FreeMonoid.ofList w) * FreeMonoid.of b) := by
      simp [atom, FreeMonoid.ofList_cons]
    _ = (atom b * P).coeff (FreeMonoid.of b * (FreeMonoid.ofList w * FreeMonoid.of b)) := by
      rw [h, mul_assoc]
    _ = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
      simp [atom, FreeMonoid.ofList_append]

theorem coeff_starts_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (v : List α) : P.coeff (FreeMonoid.ofList (a :: v)) = 0 := by
  have hz : (atom b * P).coeff (FreeMonoid.ofList (a::v) * FreeMonoid.of b) = 0 := by
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro d hd
    have hh := congrArg (fun w : FreeMonoid α => w.toList.head?) hd
    exact hab (by simpa using hh.symm)
  rw [h] at hz
  simpa [atom] using hz

theorem coeff_contains_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (u v : List α) : P.coeff (FreeMonoid.ofList (u ++ a :: v)) = 0 := by
  induction u generalizing v with
  | nil => exact coeff_starts_ne h hab v
  | cons c u ih =>
    by_cases hc : c = b
    · subst c
      rw [List.cons_append, coeff_rotate h]
      simpa [List.append_assoc] using ih (v ++ [b])
    · exact coeff_starts_ne h hc (u ++ a :: v)

theorem coeff_eq_zero_of_letter_ne {P : A α} {b a : α}
    (h : atom b * P = P * atom b) {w : List α} (ha : a ∈ w) (hab : a ≠ b) :
    P.coeff (FreeMonoid.ofList w) = 0 := by
  obtain ⟨u,v,rfl⟩ := List.append_of_mem ha
  exact coeff_contains_ne h hab u v

theorem dynkinWord_all_eq (b : α) (w : List α) (hw : ∀ a ∈ w, a = b) :
    dynkinWord w ∈ Submodule.span ℝ {FreeLieAlgebra.of ℝ b} := by
  induction w with
  | nil => simp [dynkinWord]
  | cons a w ih =>
    have ha : a = b := hw a (by simp)
    subst a
    cases w with
    | nil => exact Submodule.subset_span (by simp [dynkinWord])
    | cons c w =>
      rw [dynkinWord]
      have hmem := ih (fun a ha => hw a (by simp [ha]))
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hr, lie_smul, lie_self, smul_zero]
      exact Submodule.zero_mem _

theorem centralizer_generator {p : FL α} (b : α) (h : ⁅FreeLieAlgebra.of ℝ b,p⁆ = 0) :
    p ∈ Submodule.span ℝ {FreeLieAlgebra.of ℝ b} := by
  classical
  have hc : atom b * embed p = embed p * atom b := by
    have ht := congrArg embed h
    rw [LieHom.map_lie, embed_of, map_zero] at ht
    exact sub_eq_zero.mp ht
  rw [← normalizedDynkin_embed p, ← MonoidAlgebra.sum_coeff_single (embed p)]
  unfold Finsupp.sum
  rw [map_sum]
  apply Submodule.sum_mem
  intro w hw
  rw [normalizedDynkin, wordLinear_single]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply dynkinWord_all_eq
  intro a ha
  by_contra hab
  have hz := coeff_eq_zero_of_letter_ne hc ha hab
  have hn := Finsupp.mem_support_iff.mp hw
  exact hn (by simpa using hz)

end AssociativeModel

theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing N] [LieAlgebra ℝ N] (f : M →ₗ⁅ℝ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p

theorem eval_self : eval x y = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i <;> simp [eval, x, y]

theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]

theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)

theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp

theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]

theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℝ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℝ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))

@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _

theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h

theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h

theorem free_action_inner {R α β Z : Type*} [CommRing R]
    [LieRing Z] [LieAlgebra R Z]
    (f : FreeLieAlgebra R α →ₗ⁅R⁆ Z) (g : FreeLieAlgebra R β →ₗ⁅R⁆ Z)
    (h : FreeLieAlgebra R β →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
    (hg : ∀ b a, f (h (FreeLieAlgebra.of R b) (FreeLieAlgebra.of R a)) =
      ⁅g (FreeLieAlgebra.of R b),f (FreeLieAlgebra.of R a)⁆)
    (q : FreeLieAlgebra R β) (p : FreeLieAlgebra R α) :
    f (h q p) = ⁅g q,f p⁆ := by
  have H : ∀ q : FreeLieAlgebra R β, ∀ p : FreeLieAlgebra R α,
      f (h q p) = ⁅g q,f p⁆ := by
    intro q
    induction q using freeLie_induction with
    | h0 => intro p; simp
    | hg b =>
      intro p
      induction p using freeLie_induction with
      | h0 => simp
      | hg a => exact hg b a
      | ha p r hp hr => simp [hp,hr]
      | hs c p hp => simp [hp]
      | hl p r hp hr =>
        simp [hp,hr,LieHom.map_lie]
        grind [lie_lie,lie_skew]
    | ha q r hq hr => intro p; simp [hq,hr]
    | hs c q hq => intro p; simp [hq]
    | hl q r hq hr => intro p; simp [LieHom.map_lie,hq,hr,lie_lie]
  exact H q p

namespace InnerSemiDirect
open LieAlgebra
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)

def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel

@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]
end InnerSemiDirect

namespace SpecialFiber
open LieAlgebra FreeDerivations
abbrev F := FreeLieAlgebra ℝ (Fin 3)
def fa : F := FreeLieAlgebra.of ℝ 0
def fb : F := FreeLieAlgebra.of ℝ 1
def fc : F := FreeLieAlgebra.of ℝ 2

def action : L →ₗ⁅ℝ⁆ LieDerivation ℝ F F := eval (pair 0 1) (pair 1 2)
abbrev M := SemiDirectSum F L action

def a : M := SemiDirectSum.inl action fa
def b : M := SemiDirectSum.inl action fb
def c : M := SemiDirectSum.inl action fc
def u : M := SemiDirectSum.inr action x
def v : M := SemiDirectSum.inr action y
def w : M := -a-b-c-u-v

theorem au : ⁅a,u⁆ = -⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fa,fb]
theorem bu : ⁅b,u⁆ = ⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa,fb]
theorem cu : ⁅c,u⁆ = 0 := by
  simp only [c,u, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fc]
theorem av : ⁅a,v⁆ = 0 := by
  simp only [a,v, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa]
theorem bv : ⁅b,v⁆ = -⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fb,fc]
theorem cv : ⁅c,v⁆ = ⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fb,fc]

def chord (i j : Fin 4) : M :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => u
  | 0,3 | 3,0 => w
  | 1,2 | 2,1 => b
  | 1,3 | 3,1 => c
  | 2,3 | 3,2 => v
  | _,_ => 0

private theorem chord_symm (i j : Fin 4) : chord i j = chord j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem chord_zero (i : Fin 4) : chord i i = 0 := by fin_cases i <;> rfl

private theorem chord_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ⁅chord i j,chord k l⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals fin_cases l <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie,
    bu,cu,av,bv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

private theorem chord_three (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord i j,chord i k+chord j k⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie, lie_add,
    au,bu,cu,av,bv,cv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]

def representation : T4 →ₗ⁅ℝ⁆ M :=
  T4Universal.lift chord chord_symm chord_zero chord_disjoint chord_three

@[simp] theorem representation_t (i j : Fin 4) : representation (t i j) = chord i j :=
  T4Universal.lift_t _ _ _ _ _ _ _

def fiberSpec : F →ₗ⁅ℝ⁆ L := FreeLieAlgebra.lift ℝ
  (fun i => if i = 0 then x else if i = 1 then y else -x-y)
def baseSpec : L →ₗ⁅ℝ⁆ L := eval (-x-y) x

@[simp] theorem fiberSpec_fa : fiberSpec fa = x := by simp [fiberSpec,fa]
@[simp] theorem fiberSpec_fb : fiberSpec fb = y := by simp [fiberSpec,fb]
@[simp] theorem fiberSpec_fc : fiberSpec fc = -x-y := by simp [fiberSpec,fc]
@[simp] theorem baseSpec_x : baseSpec x = -x-y := eval_x _ _
@[simp] theorem baseSpec_y : baseSpec y = x := eval_y _ _

theorem spec_equivariant (q : L) (p : F) :
    fiberSpec (action q p) = ⁅baseSpec q,fiberSpec p⁆ := by
  apply free_action_inner
  intro i j
  cases i <;> fin_cases j <;>
    simp [action, eval, baseSpec, fiberSpec, FreeDerivations.pair,
      x,y,sub_lie,neg_lie,lie_sub,lie_neg]

def specialize : M →ₗ⁅ℝ⁆ L := InnerSemiDirect.lift action fiberSpec baseSpec spec_equivariant

@[simp] theorem specialize_a : specialize a = x := by simp [specialize,a, InnerSemiDirect.lift]
@[simp] theorem specialize_b : specialize b = y := by simp [specialize,b, InnerSemiDirect.lift]
@[simp] theorem specialize_c : specialize c = -x-y := by simp [specialize,c, InnerSemiDirect.lift]
@[simp] theorem specialize_u : specialize u = -x-y := by simp [specialize,u, InnerSemiDirect.lift]
@[simp] theorem specialize_v : specialize v = x := by simp [specialize,v, InnerSemiDirect.lift]

@[simp] theorem eval_right (d e : M) (p : L) :
    (eval d e p).right = eval d.right e.right p :=
  map_eval (SemiDirectSum.projr action) d e p

def Fa (p : L) : F := (eval (u+b) v p - eval u v p).left
def Fb (p : L) : F := (eval (u+a) (v+c) p - eval u v p).left
def Fc (p : L) : F := (eval u (v+b) p - eval u v p).left

 theorem Fa_inl (p : L) : SemiDirectSum.inl action (Fa p) = eval (u+b) v p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]
 theorem Fb_inl (p : L) : SemiDirectSum.inl action (Fb p) = eval (u+a) (v+c) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,a,v,c]
 theorem Fc_inl (p : L) : SemiDirectSum.inl action (Fc p) = eval u (v+b) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]

theorem eval_comm_a (p : L) : ⁅a,eval (u+b) v p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,au]; exact neg_add_cancel _
  · exact av
theorem eval_comm_b (p : L) : ⁅b,eval (u+a) (v+c) p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,bu]; grind [lie_skew]
  · rw [lie_add,bv]; exact neg_add_cancel _
theorem eval_comm_c (p : L) : ⁅c,eval u (v+b) p⁆ = 0 := by
  apply eval_commutes
  · exact cu
  · rw [lie_add,cv]; grind [lie_skew]
theorem eval_comm_sum (p : L) : ⁅a+b+c,eval u v p⁆ = 0 := by
  apply eval_commutes
  · rw [add_lie,add_lie,au,bu,cu]; abel
  · rw [add_lie,add_lie,av,bv,cv]; abel

theorem fiber_identity (p : L) :
    ⁅fa+fb+fc,Fb p⁆ = ⁅fa,Fb p-Fa p⁆ + ⁅fc,Fb p-Fc p⁆ := by
  apply SemiDirectSum.inl_injective action
  simp only [LieHom.map_lie, map_add, map_sub, Fa_inl,Fb_inl,Fc_inl]
  change ⁅a+b+c,eval (u+a) (v+c) p - eval u v p⁆ =
    ⁅a,(eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p)⁆ +
    ⁅c,(eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p)⁆
  rw [lie_sub,eval_comm_sum]
  simp only [lie_sub,add_lie,eval_comm_a,eval_comm_b,eval_comm_c]
  abel

theorem Fb_specialize {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    fiberSpec (Fb p) = -eval (-x-y) x p := by
  have H := congrArg specialize (Fb_inl p)
  rw [show specialize (SemiDirectSum.inl action (Fb p)) = fiberSpec (Fb p) from
    InnerSemiDirect.lift_inl _ _ _ _ _] at H
  simp only [map_sub,map_eval,map_add,specialize_u,specialize_a,specialize_v,specialize_c] at H
  have ha : -x-y+x = -y := by abel
  have hb : x+(-x-y) = -y := by abel
  rw [ha,hb,eval_vanish_of_commuting (-y) (-y) (lie_self _) hp hn,zero_sub] at H
  exact H

theorem pentagon {p : L} (hp : p ∈ W) :
    eval a (b+c) p + eval (u+b) v p =
    eval b v p + eval (a+u) (c+v) p + eval a b p := by
  have h := congrArg representation hp.2.2
  simpa [map_eval,chord] using h

theorem pentagon_reverse {p : L} (hp : p ∈ W) :
    eval c (b+a) p + eval (v+b) u p =
    eval b u p + eval (c+v) (a+u) p + eval c b p := by
  have h := congrArg (representation.comp (t4Rename (Equiv.swap 0 3))) hp.2.2
  simp only [LieHom.comp_apply,map_add,map_eval,t4Rename_t,representation_t] at h
  exact h

theorem eval_bv_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b v p = eval b (-b-c) p := by
  have H := eval_central_shift b (-b-c) (v+b+c) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-c+(v+b+c) = v := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bv]
    abel
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bv,cv]
    grind [lie_skew]

theorem eval_bu_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b u p = eval b (-b-a) p := by
  have H := eval_central_shift b (-b-a) (u+b+a) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-a+(u+b+a) = u := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bu]
    grind [lie_skew]
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bu,au]
    grind [lie_skew]

theorem delta_a {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fa p = eval fa (fb+fc) p - eval fa fb p - eval fb (-fb-fc) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fa_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p) =
    eval a (b+c) p - eval a b p - eval b (-b-c) p
  have H := pentagon hp
  rw [eval_bv_shift hpn hn,add_comm a u,add_comm c v] at H
  grind only

theorem delta_c {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fc p = -eval fc (fa+fb) p + eval fc fb p + eval fb (-fb-fa) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fc_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p) =
    -eval c (a+b) p + eval c b p + eval b (-b-a) p
  have H := pentagon_reverse hp
  rw [eval_bu_shift hpn hn,solution_swap hp (v+b) u,solution_swap hp (c+v) (a+u),
    add_comm b a,add_comm a u,add_comm c v] at H
  grind only

end SpecialFiber

namespace Differentiation
open FreeDerivations

variable {M N : Type} [LieRing M] [LieAlgebra ℝ M] [LieRing N] [LieAlgebra ℝ N]

@[simp] theorem Jet.base_neg (p : Jet ℝ M) : (-p).base = -p.base := rfl
@[simp] theorem Jet.velocity_neg (p : Jet ℝ M) : (-p).velocity = -p.velocity := rfl
@[simp] theorem Jet.base_sub (p q : Jet ℝ M) : (p-q).base = p.base-q.base := rfl
@[simp] theorem Jet.velocity_sub (p q : Jet ℝ M) : (p-q).velocity = p.velocity-q.velocity := rfl

@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℝ M) = Jet.mk (-a) (-da) := rfl
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl

@[simp] theorem eval_base (a b : Jet ℝ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p

def adPower (a : M) : ℕ → M → M
  | 0, t => t
  | n+1, t => ⁅a,adPower a n t⁆

omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero (a t : M) : adPower a 0 t = t := rfl
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_succ (a t : M) (n : ℕ) : adPower a (n+1) t = ⁅a,adPower a n t⁆ := rfl
@[simp] theorem adPower_smul (a t : M) (n : ℕ) (r : ℝ) :
    adPower a n (r • t) = r • adPower a n t := by
  induction n <;> simp_all
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero_right (a : M) (n : ℕ) : adPower a n 0 = 0 := by
  induction n <;> simp_all
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_self (a : M) {n : ℕ} (hn : 0<n) : adPower a n a = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih => simp_all
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero_left (t : M) {n : ℕ} (hn : 0<n) : adPower (0:M) n t = 0 := by
  cases n <;> simp_all

def slope (p : L) (a b da db : M) : M :=
  (eval (Jet.mk a da : Jet ℝ M) (Jet.mk b db) p).velocity

@[simp] theorem slope_x (a b da db : M) : slope x a b da db = da := by simp [slope]
@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]
@[simp] theorem slope_zero (a b da db : M) : slope 0 a b da db = 0 := by simp [slope]
@[simp] theorem slope_add (p q : L) (a b da db : M) :
    slope (p+q) a b da db = slope p a b da db + slope q a b da db := by simp [slope]
@[simp] theorem slope_smul (r : ℝ) (p : L) (a b da db : M) :
    slope (r • p) a b da db = r • slope p a b da db := by simp [slope]
@[simp] theorem slope_lie (p q : L) (a b da db : M) :
    slope ⁅p,q⁆ a b da db = ⁅slope p a b da db,eval a b q⁆ +
      ⁅eval a b p,slope q a b da db⁆ := by simp [slope,LieHom.map_lie]

@[simp] theorem slope_zero_direction (p : L) (a b : M) : slope p a b 0 0 = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq]

theorem slope_add_direction (p : L) (a b da db ea eb : M) :
    slope p a b (da+ea) (db+eb) = slope p a b da db + slope p a b ea eb := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq => simp [hp,hq,add_lie,lie_add]; abel

theorem slope_smul_direction (p : L) (a b da db : M) (r : ℝ) :
    slope p a b (r • da) (r • db) = r • slope p a b da db := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,smul_add]
  | hs s p hp => simp [hp,smul_comm s r]
  | hl p q hp hq => simp [hp,hq,smul_add]

theorem word_pos {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) : 0<n := by
  induction hp with
  | generator => omega
  | bracket hp hq ihp ihq => omega

def DiagonalData (n : ℕ) (p : L) (s k : ℝ) : Prop :=
  (n ≠ 1 → s = 0) ∧ ∀ (M : Type) [LieRing M] [LieAlgebra ℝ M] (a t : M),
    eval (Jet.mk a 0 : Jet ℝ M) (Jet.mk (-a) t) p =
      Jet.mk (s • a) (k • adPower a (n-1) t)

theorem diagonal_bracket {n m : ℕ} {p q : L} {s k t l : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hp : DiagonalData n p s k) (hq : DiagonalData m q t l) :
    ∃ r : ℝ, DiagonalData (n+m) ⁅p,q⁆ 0 r := by
  rcases hp with ⟨hs,hp⟩
  rcases hq with ⟨ht,hq⟩
  by_cases hn1 : n=1 <;> by_cases hm1 : m=1
  · subst n; subst m
    refine ⟨s*l-t*k, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · change ⁅k • b,t • a⁆ + ⁅s • a,l • b⁆ = (s*l-t*k) • ⁅a,b⁆
      rw [smul_lie,lie_smul,←lie_skew b a,smul_neg,smul_lie,lie_smul]
      simp only [sub_smul,mul_smul]
      module
  · subst n
    have ht0 := ht hm1
    subst t
    refine ⟨s*l, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : 1+m-1 = (m-1)+1 := by omega
      simp [he,mul_smul,smul_comm l s]
  · subst m
    have hs0 := hs hn1
    subst s
    refine ⟨-(t*k), fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : n+1-1 = (n-1)+1 := by omega
      simp only [Jet.velocity_lie,zero_smul,zero_lie,he,adPower_succ,
        smul_lie,lie_smul,neg_smul,mul_smul]
      rw [←lie_skew (adPower a (n-1) b) a,smul_neg,smul_neg]
      rw [smul_comm]
      simp
  · have hs0 := hs hn1
    have ht0 := ht hm1
    subst s; subst t
    refine ⟨0, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext <;> simp

theorem diagonal_word {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) :
    ∃ s k : ℝ, DiagonalData n p s k := by
  induction hp with
  | generator i =>
    cases i
    · refine ⟨1,0, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
    · refine ⟨-1,1, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
  | bracket hp hq ihp ihq =>
    rcases ihp with ⟨s,k,hp'⟩
    rcases ihq with ⟨t,l,hq'⟩
    obtain ⟨r,hr⟩ := diagonal_bracket (word_pos hp) (word_pos hq) hp' hq'
    exact ⟨0,r,hr⟩

theorem diagonal_homogeneous {n : ℕ} {p : L} (hp : p ∈ Ln n) :
    ∃ s k : ℝ, DiagonalData n p s k := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact diagonal_word hp
  | zero =>
    refine ⟨0,0,fun _ => rfl,?_⟩
    intro M _ _ a b
    ext <;> simp
  | add p q _ _ hp hq =>
    rcases hp with ⟨s,k,hs,hp⟩
    rcases hq with ⟨t,l,ht,hq⟩
    refine ⟨s+t,k+l,fun hn => by simp [hs hn,ht hn],?_⟩
    intro M _ _ a b
    rw [map_add,hp,hq]
    ext <;> simp [add_smul]
  | smul r p _ hp =>
    rcases hp with ⟨s,k,hs,hp⟩
    refine ⟨r*s,r*k,fun hn => by simp [hs hn],?_⟩
    intro M _ _ a b
    rw [map_smul,hp]
    ext <;> simp [mul_smul]

 theorem slope_neg_direction (p : L) (a b da db : M) :
    slope p a b (-da) (-db) = -slope p a b da db := by
  simpa using slope_smul_direction p a b da db (-1)

 theorem slope_inner (p : L) (a b t : M) :
    slope p a b ⁅t,a⁆ ⁅t,b⁆ = ⁅t,eval a b p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq,LieHom.map_lie,lie_lie]

 theorem slope_swap {p : L} (hp : p ∈ W) (a b da db : M) :
    slope p a b da db = -slope p b a db da := by
  exact congrArg Jet.velocity (solution_swap hp (Jet.mk a da : Jet ℝ M) (Jet.mk b db))

 theorem diagonal_slope {n : ℕ} {p : L} {s k : ℝ}
    (hp : DiagonalData n p s k) (a t : M) :
    slope p a (-a) 0 t = k • adPower a (n-1) t :=
  congrArg Jet.velocity (hp.2 M a t)

 theorem diagonal_first {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a t : M) :
    slope p a (-a) t 0 = slope p a (-a) 0 t := by
  have H := congrArg Jet.velocity (eval_vanish_of_commuting
    (Jet.mk a t : Jet ℝ M) (-Jet.mk a t) (by rw [lie_neg,lie_self,neg_zero]) hp hn)
  change slope p a (-a) t (-t) = 0 at H
  have hs := slope_add_direction p a (-a) t 0 0 (-t)
  have hneg := slope_neg_direction p a (-a) 0 t
  simp only [neg_zero] at hneg
  simp only [add_zero,zero_add,hneg,H] at hs
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hs.symm)

 def G (p : L) : L := ⁅x,eval y x p⁆ + ⁅-x-y,eval y (-x-y) p⁆

 theorem eval_G (p : L) (a b : M) :
    eval a b (G p) = ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ := by
  simp only [G,map_add,LieHom.map_lie,map_eval,eval_x,eval_y,map_sub,map_neg]

 theorem slope_G (p : L) (a b t : M) :
    slope (G p) a b t 0 =
      ⁅t,eval b a p-eval b (-a-b) p⁆ +
      ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have hh := congrArg Jet.velocity (eval_G p (Jet.mk a t : Jet ℝ M) (Jet.mk b 0))
  change slope (G p) a b t 0 = _ at hh
  simp only [Jet.mk_neg,Jet.mk_sub,sub_zero] at hh
  simp only [Jet.velocity_add,Jet.velocity_lie,eval_base] at hh
  have he : slope p b (-a-b) 0 (-t) = -slope p b (-a-b) 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b (-a-b) 0 t
  change slope (G p) a b t 0 = ⁅t,eval b a p⁆ + ⁅a,slope p b a 0 t⁆ +
    (⁅-t,eval b (-a-b) p⁆ + ⁅-a-b,slope p b (-a-b) 0 (-t)⁆) at hh
  rw [he,neg_lie,lie_neg] at hh
  rw [lie_sub]
  grind only

 def fiberEval (a b c : M) : SpecialFiber.F →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun i => if i=0 then a else if i=1 then b else c)
@[simp] theorem fiberEval_fa (a b c : M) : fiberEval a b c SpecialFiber.fa = a := by
  simp [fiberEval,SpecialFiber.fa]
@[simp] theorem fiberEval_fb (a b c : M) : fiberEval a b c SpecialFiber.fb = b := by
  simp [fiberEval,SpecialFiber.fb]
@[simp] theorem fiberEval_fc (a b c : M) : fiberEval a b c SpecialFiber.fc = c := by
  simp [fiberEval,SpecialFiber.fc]

 theorem fiberEval_spec (a b : M) (z : SpecialFiber.F) :
    fiberEval a b (-a-b) z = eval a b (SpecialFiber.fiberSpec z) := by
  have h : fiberEval a b (-a-b) = (eval a b).comp SpecialFiber.fiberSpec := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,SpecialFiber.fiberSpec]
  exact LieHom.congr_fun h z

@[simp] theorem fiberEval_base (a b c : Jet ℝ M) (z : SpecialFiber.F) :
    (fiberEval a b c z).base = fiberEval a.base b.base c.base z := by
  have h : Jet.baseHom.comp (fiberEval a b c) = fiberEval a.base b.base c.base := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,Jet.baseHom] <;> rfl
  exact LieHom.congr_fun h z

 theorem fiberEval_Fb {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a b : M) :
    fiberEval a b (-a-b) (SpecialFiber.Fb p) = - eval (-a-b) a p := by
  rw [fiberEval_spec,SpecialFiber.Fb_specialize hp hn]
  simp [map_eval]

 theorem transverse {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    -⁅t,eval (-a-b) a p⁆ = k • (adPower a n t-adPower (-a-b) n t) +
       ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have H := congrArg (fiberEval (Jet.mk a 0 : Jet ℝ M) (Jet.mk b 0)
    (Jet.mk (-a-b) t)) (SpecialFiber.fiber_identity p)
  rw [SpecialFiber.delta_a hp hpn hn,SpecialFiber.delta_c hp hpn hn] at H
  simp only [LieHom.map_lie,map_add,map_sub,map_neg,map_eval,
    fiberEval_fa,fiberEval_fb,fiberEval_fc] at H
  have hc : (Jet.mk a 0 : Jet ℝ M) + Jet.mk b 0 + Jet.mk (-a-b) t = Jet.mk 0 t := by
    ext <;> simp
  rw [hc] at H
  simp only [Jet.mk_add,Jet.mk_neg,Jet.mk_sub,zero_add,add_zero,neg_zero,sub_zero,zero_sub] at H
  have Hv := congrArg Jet.velocity H
  simp only [Jet.velocity_lie,Jet.velocity_sub,Jet.velocity_add,Jet.velocity_neg,
    Jet.base_add,Jet.base_sub,Jet.base_neg,eval_base,fiberEval_base] at Hv
  have hdiagNeg : -(-a-b) = a+b := by abel
  have hba : b+(-a-b) = -a := by abel
  have hab : -b-(-a-b) = a := by abel
  have hc0 : eval (-a-b) (a+b) p = 0 := by
    have h := eval_vanish_of_commuting (-a-b) (-(-a-b)) (by simp only [lie_neg,lie_self,neg_zero]) hpn hn
    simpa only [hdiagNeg] using h
  have hdelc : -eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p = 0 := by
    rw [hc0,neg_zero,zero_add,solution_swap hp (-a-b) b]
    have he : -b-a = -a-b := by abel
    rw [he,neg_add_cancel]
  have hdp : slope p (-a-b) (a+b) t 0 = k • adPower (-a-b) (n-1) t := by
    rw [← hdiagNeg,diagonal_first hpn hn,diagonal_slope hdiag]
  have hdm : slope p b a 0 (-t) = -slope p b a 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b a 0 t
  have hswap := slope_swap hp (-a-b) b t 0
  have hnp : n=(n-1)+1 := by omega
  change ⁅t,fiberEval a b (-a-b) (SpecialFiber.Fb p)⁆ + ⁅(0:M),_⁆ =
    (⁅(0:M),_⁆ + ⁅a,slope p a (b+(-a-b)) 0 t - slope p a b 0 0 -
      slope p b (-b-(-a-b)) 0 (-t)⁆) +
    (⁅t,-eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p⁆ +
      ⁅-a-b,-slope p (-a-b) (a+b) t 0 + slope p (-a-b) b t 0 +
        slope p b (-b-a) 0 0⁆) at Hv
  rw [fiberEval_Fb hpn hn,hdelc,hba,hab,slope_zero_direction,slope_zero_direction,
    diagonal_slope hdiag,hdp,hdm,hswap] at Hv
  simp only [zero_lie,lie_zero,add_zero,zero_add,sub_zero,lie_neg,lie_sub,lie_add,lie_smul] at Hv
  rw [show ⁅a,adPower a (n-1) t⁆ = adPower a n t by rw [hnp]; rfl,
    show ⁅-a-b,adPower (-a-b) (n-1) t⁆ = adPower (-a-b) n t by rw [hnp]; rfl] at Hv
  rw [smul_sub]
  grind only

 theorem slope_G_formula {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    slope (G p) a b t 0 = - k • (adPower a n t-adPower (-a-b) n t) := by
  have H := transverse hp hpn hn hdiag a b t
  have h3 := solution_three hp a b
  rw [solution_swap hp a b] at h3
  have he : eval b a p - eval b (-a-b) p = eval (-a-b) a p := by grind only
  rw [slope_G,he,neg_smul]
  grind only

def swapJet : Jet ℝ (Jet ℝ M) →ₗ⁅ℝ⁆ Jet ℝ (Jet ℝ M) where
  toFun z := ⟨⟨z.base.base,z.velocity.base⟩,⟨z.base.velocity,z.velocity.velocity⟩⟩
  map_add' a b := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_smul' r a := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_lie' {a b} := by
    apply Jet.ext <;> apply Jet.ext
    all_goals simp only [Jet.base_lie,Jet.velocity_lie,Jet.base_add,Jet.velocity_add]
    all_goals first | rfl | abel

theorem mixed_slope (p : L) (a b u v : M) :
    (slope p (Jet.mk a u : Jet ℝ M) (Jet.mk b 0) (Jet.mk v 0) 0).velocity =
    (slope p (Jet.mk a v : Jet ℝ M) (Jet.mk b 0) (Jet.mk u 0) 0).velocity := by
  have h := map_eval (swapJet : Jet ℝ (Jet ℝ M) →ₗ⁅ℝ⁆ Jet ℝ (Jet ℝ M))
    (Jet.mk (Jet.mk a u) (Jet.mk v 0)) (Jet.mk (Jet.mk b 0) 0) p
  exact congrArg (fun z => z.velocity.velocity) h

@[simp] theorem adPower_base (a t : Jet ℝ M) (n : ℕ) :
    (adPower a n t).base = adPower a.base n t.base := by
  induction n <;> simp_all

theorem adPower_radial (a t : M) (n : ℕ) :
    (adPower (Jet.mk a a : Jet ℝ M) n (Jet.mk t 0)).velocity =
      (n : ℝ) • adPower a n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,ih,lie_smul,
      Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel

theorem adPower_transverse_self (a t : M) {n : ℕ} (hn : 0<n) :
    (adPower (Jet.mk a t : Jet ℝ M) n (Jet.mk a 0)).velocity = -adPower a n t := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [lie_skew]
    | succ n ih =>
      rw [adPower_succ,Jet.velocity_lie,adPower_base]
      change ⁅t,adPower a (n+1) a⁆ +
        ⁅a,(adPower (Jet.mk a t : Jet ℝ M) (n+1) (Jet.mk a 0)).velocity⁆ = _
      rw [adPower_self a (n := n+1) (by omega),lie_zero,zero_add,ih (by omega),lie_neg]
      rfl

theorem adPower_zero_base (a t : M) {n : ℕ} (hn : 1<n) :
    (adPower (Jet.mk 0 a : Jet ℝ M) n (Jet.mk t 0)).velocity = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,zero_lie,add_zero]
    rw [adPower_zero_left t (by omega),lie_zero]

 theorem mixed_scalar {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) (a t : M) :
    (((n : ℝ)+1)*k) • adPower a n t = 0 := by
  have H1 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a a : Jet ℝ M) (Jet.mk (-a) 0) (Jet.mk t 0))
  have H2 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a t : Jet ℝ M) (Jet.mk (-a) 0) (Jet.mk a 0))
  have hc1 : -(Jet.mk a a : Jet ℝ M) - Jet.mk (-a) 0 = Jet.mk 0 (-a) := by
    ext <;> simp
  have hc2 : -(Jet.mk a t : Jet ℝ M) - Jet.mk (-a) 0 = Jet.mk 0 (-t) := by
    ext <;> simp
  rw [hc1] at H1
  rw [hc2] at H2
  simp only [Jet.velocity_smul,Jet.velocity_sub,adPower_radial,
    adPower_zero_base (-a) t (n := n) (by omega),sub_zero] at H1
  simp only [Jet.velocity_smul,Jet.velocity_sub,
    adPower_transverse_self a t (n := n) (by omega),adPower_zero_base (-t) a (n := n) (by omega),sub_zero] at H2
  have hm := mixed_slope (G p) a (-a) a t
  rw [H1,H2] at hm
  have hz : (-k) • ((n:ℝ) • adPower a n t) - (-k) • (-adPower a n t) = 0 := sub_eq_zero.mpr hm
  calc
    (((n : ℝ)+1)*k) • adPower a n t =
        -((-k) • ((n:ℝ) • adPower a n t) - (-k) • (-adPower a n t)) := by module
    _ = 0 := by rw [hz,neg_zero]

 theorem diagonal_scalar_zero {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) : k=0 := by
  let := LieRing.ofAssociativeRing (A := Matrix (Fin 2) (Fin 2) ℝ)
  let a : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
  let t : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]
  have hbr : ⁅a,t⁆ = t := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a,t,Ring.lie_def,Matrix.mul_apply,Fin.sum_univ_two]
  have had (m : ℕ) : adPower a m t = t := by
    induction m with
    | zero => rfl
    | succ m ih => rw [adPower_succ,ih,hbr]
  have H := mixed_scalar hp hpn hn hdiag a t
  rw [had] at H
  have hc := congrArg (fun z => z 0 1) H
  change (((n : ℝ)+1)*k) * 1 = 0 at hc
  rw [mul_one] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by positivity)

 theorem special_G_zero {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) : G p = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  subst k
  have hder (t : L) : slope (G p) x y t 0 = 0 := by
    rw [slope_G_formula hp hpn (by omega) hd]
    simp
  have hcomm : ⁅y,G p⁆ = 0 := by
    have h := slope_inner (G p) x y y
    rw [lie_self,eval_self,LieHom.id_apply] at h
    rw [← h,hder]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (AssociativeModel.centralizer_generator true hcomm)
  change r • y = G p at hr
  have he : eval (0 : L) y (G p) = 0 := by
    rw [eval_G]
    simp only [zero_lie,neg_zero,zero_sub,zero_add]
    rw [eval_vanish_of_commuting y (-y) (by simp) hpn (by omega),lie_zero]
  rw [← hr,map_smul,eval_y] at he
  exact hr.symm.trans he

 theorem special_identity_oai {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a b : M) : ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ = 0 := by
  rw [← eval_G,special_G_zero hp hpn hn,map_zero]

end Differentiation
end RealDeligneDrinfeld

end

end OAI

end













section
open OAI.RealDeligneDrinfeld.Differentiation in
theorem solution : ∀ {M : Type} [LieRing M] [LieAlgebra ℝ M] {n : ℕ}
    {p : OAI.RealDeligneDrinfeld.L} (hp : p ∈ OAI.RealDeligneDrinfeld.W) (hpn : p ∈ OAI.RealDeligneDrinfeld.Ln n)
    (hn : 2 < n) (a b : M),
    ⁅a, (OAI.RealDeligneDrinfeld.eval b a) p⁆ + ⁅-a - b, (OAI.RealDeligneDrinfeld.eval b (-a - b)) p⁆ = 0 :=
  @OAI.RealDeligneDrinfeld.Differentiation.special_identity_oai
end
