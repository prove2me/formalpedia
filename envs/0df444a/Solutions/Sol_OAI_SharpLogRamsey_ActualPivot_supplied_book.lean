-- Prove2me | solution 1 for OAI.SharpLogRamsey.ActualPivot.supplied_book
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:31:42.985564+00:00
-- url     : https://prove2.me/submissions/52eb2f73-a885-4854-ab7a-89513e828ee8

import Mathlib
import Definitions.Def_OAIQ045S002
import Theorems.Thm_OAI_SharpLogRamsey_GeometricCover_uniform_four

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_EightIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.CapComposition
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

lemma powers_step (L : Finset (Finset α)) (U A D : Finset α) (k : ℕ)
    (hA : A ∈ powers L U k) (hD : D ∈ L) : A∩D ∈ powers L U (k+1) :=
  mem_biUnion.mpr ⟨A,hA,mem_image.mpr ⟨D,hD,rfl⟩⟩

lemma powers_card (L : Finset (Finset α)) (U : Finset α) (k : ℕ) :
    (powers L U k).card ≤ L.card^k := by
  induction k with
  | zero => simp [powers]
  | succ k ih =>
    calc
      _  ≤  ∑ A ∈ powers L U k,(L.image (fun D => A∩D)).card := card_biUnion_le
      _  ≤  ∑ _A ∈ powers L U k,L.card := sum_le_sum (fun A hA => card_image_le)
      _ = (powers L U k).card*L.card := by simp
      _  ≤  L.card^k*L.card := Nat.mul_le_mul_right _ ih
      _ = _ := (pow_succ _ _).symm

lemma loss_inter (S A D : Finset α) :
    (S\(A∩D)).card ≤ (S\A).card+(S\D).card := by
  have he : S\(A∩D)=(S\A)∪(S\D) := by ext x; simp; tauto
  rw [he]
  exact card_union_le _ _

lemma remains_nonempty (S A : Finset α) (hS : S.Nonempty) (δ : ℝ) (hδ : δ < 1)
    (hloss : ((S\A).card:ℝ) ≤ δ*S.card) : A.Nonempty := by
  by_contra h
  have he : A=∅ := not_nonempty_iff_eq_empty.mp h
  rw [he,sdiff_empty] at hloss
  have hs : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  nlinarith

theorem eight_intersections (U S : Finset α) (hS : S.Nonempty) (hSU : S ⊆ U)
    (L : Finset (Finset α)) (m q ρ : ℝ) (hm : 0 ≤ m) (_hq : 0 ≤ q)
    (hρ : 0 ≤ ρ) (hρhalf : ρ ≤ 1/2) (hρpow : q*ρ^7 ≤ 1)
    (hfirst : ∀ D ∈ L,(D.card:ℝ) ≤ q*m)
    (hstep : ∀ A,A ⊆ U → A.Nonempty → ∃ D ∈ L,D ⊆ U ∧
      ((S\D).card:ℝ) ≤ (3/100:ℝ)*S.card ∧
      ((A∩D).card:ℝ) ≤ m+ρ*A.card) :
    ∃ A ∈ powers L U 8,A ⊆ U ∧ (A.card:ℝ) ≤ 3*m ∧ (S.card:ℝ)/2 ≤ (S∩A).card := by
  have hU : U.Nonempty := hS.mono hSU
  obtain ⟨D,hD,hDU,hloss,_hcont⟩ := hstep U Subset.rfl hU
  have hinit : D ∈ powers L U 1 := by
    have hh := powers_step L U U D 0 (by simp [powers]) hD
    simpa only [inter_eq_right.mpr hDU] using hh
  have hex : ∀ r : ℕ,r ≤ 7 → ∃ A ∈ powers L U (r+1),A ⊆ U ∧
      ((S\A).card:ℝ) ≤ ((r:ℝ)+1)*(3/100:ℝ)*S.card ∧
      (A.card:ℝ) ≤ 2*m+q*m*ρ^r := by
    intro r
    induction r with
    | zero =>
      intro hr
      refine ⟨D,hinit,hDU,by simpa using hloss,?_⟩
      have hh := hfirst D hD
      simpa only [pow_zero,mul_one] using hh.trans (by linarith : q*m ≤ 2*m+q*m)
    | succ r ih =>
      intro hr
      obtain ⟨A,hA,hAU,hl,hsize⟩ := ih (by omega)
      have hAne : A.Nonempty := remains_nonempty S A hS (((r:ℝ)+1)*(3/100:ℝ))
        (by
          have hh : (r:ℝ) ≤ 6 := by exact_mod_cast (by omega : r ≤ 6)
          linarith) hl
      obtain ⟨E,hE,_hEU,hEl,hEc⟩ := hstep A hAU hAne
      refine ⟨A∩E,powers_step L U A E (r+1) hA hE,inter_subset_left.trans hAU,?_,?_⟩
      · have hh : ((S\(A∩E)).card:ℝ) ≤ (S\A).card+(S\E).card := by exact_mod_cast loss_inter S A E
        push_cast
        linarith
      · have hh := mul_le_mul_of_nonneg_left hsize hρ
        rw [pow_succ]
        have hb : 2*m*ρ ≤ m := by nlinarith
        nlinarith
  obtain ⟨A,hA,hAU,hl,hsize⟩ := hex 7 (le_refl _)
  refine ⟨A,hA,hAU,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right hρpow hm
    nlinarith
  · have he : ((S\A).card:ℝ)+(S∩A).card=S.card := by exact_mod_cast card_sdiff_add_card_inter S A
    norm_num at hl
    linarith

end
end SharpLogRamsey.CapComposition

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Reciprocal_LevelLosses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Incidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_incident_points [Finite K] [FiniteDimensional K V] {d : ℕ}
    (hdim : Module.finrank K V = d+1)
    (b : Projectivization K (Module.Dual K V)) :
    Nat.card {a : Projectivization K V // Incident a b} =
      ∑ i ∈ Finset.range d, Nat.card K ^ i := by
  let e : {a : Projectivization K V // Incident a b} ≃
      {a : Projectivization K V // a.submodule ≤ LinearMap.ker b.rep} :=
    Equiv.subtypeEquivRight (fun a => incident_iff_submodule a b)
  rw [Nat.card_congr e, ← Nat.card_congr (projectiveSubmoduleEquiv (LinearMap.ker b.rep))]
  apply Projectivization.card_of_finrank
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  omega

end SharpLogRamsey.Incidence

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma quotient_dimension [FiniteDimensional K V] (z : Projectivization K V) :
    Module.finrank K (V ⧸ z.submodule)+1 = Module.finrank K V := by
  simpa only [Projectivization.finrank_submodule] using z.submodule.finrank_quotient_add_finrank

lemma incident_mk_iff (v : V) (hv : v ≠ 0) (f : Module.Dual K V) (hf : f ≠ 0) :
    SharpLogRamsey.Incidence.Incident (Projectivization.mk K v hv) (Projectivization.mk K f hf) ↔ f v = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  unfold SharpLogRamsey.Incidence.Incident
  rw [← ha,← hb]
  simp [Units.smul_def]

lemma project_incident_iff (z : Projectivization K V)
    (p : {p : Projectivization K V // p ≠ z})
    (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
    SharpLogRamsey.Incidence.Incident (project z p) (projectDual z t) ↔ SharpLogRamsey.Incidence.Incident p.val t.val := by
  rw [project,projectDual,incident_mk_iff]
  rfl

lemma projectDual_injective (z : Projectivization K V) : Function.Injective (projectDual z) := by
  intro t u h
  apply Subtype.ext
  have hh := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  obtain ⟨a,ha⟩ := hh
  rw [← t.val.mk_rep,← u.val.mk_rep,Projectivization.mk_eq_mk_iff']
  refine ⟨a,?_⟩
  ext v
  exact congrArg (fun f : Module.Dual K (V ⧸ z.submodule) => f (z.submodule.mkQ v)) ha

lemma collision_center_on_line (z : Projectivization K V)
    (p q : {p : Projectivization K V // p ≠ z})
    (hpq : p.val ≠ q.val) (h : project z p = project z q) :
    z.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hker : p.val.rep-a • q.val.rep ∈ LinearMap.ker z.submodule.mkQ := by
    change z.submodule.mkQ (p.val.rep-a • q.val.rep) = 0
    rw [map_sub,map_smul,ha,sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hne : p.val.rep-a • q.val.rep ≠ 0 := by
    intro he
    apply hpq
    rw [← p.val.mk_rep,← q.val.mk_rep,Projectivization.mk_eq_mk_iff']
    exact ⟨a,(sub_eq_zero.mp he).symm⟩
  let r := Projectivization.mk K (p.val.rep-a • q.val.rep) hne
  have hr : r = z := by
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
      exact hker
    · simp only [Projectivization.finrank_submodule]
  have hline : r.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
    rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    apply Submodule.sub_mem
    · apply (le_sup_left : p.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    · apply Submodule.smul_mem
      apply (le_sup_right : q.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
  exact (congrArg Projectivization.submodule hr).symm.le.trans hline

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma joining_line_finrank (p q : Projectivization K V) (hpq : p ≠ q) :
    Module.finrank K ↥(p.submodule ⊔ q.submodule : Submodule K V) = 2 := by
  have h := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hpq)
  rw [Matrix.range_cons_cons_empty] at h
  rw [Submodule.span_insert] at h
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact h

lemma joining_line_card [Finite K] (p q : Projectivization K V) (hpq : p ≠ q) :
    Nat.card {z : Projectivization K V // z.submodule ≤ p.submodule ⊔ q.submodule} =
      Nat.card K+1 := by
  rw [← Nat.card_congr (_root_.OAI.SharpLogRamsey.Incidence.projectiveSubmoduleEquiv (p.submodule ⊔ q.submodule))]
  exact Projectivization.card_of_finrank_two K _ (joining_line_finrank p q hpq)

lemma collides_on_line (z p q : Projectivization K V) (hpq : p ≠ q) (h : Collides z p q) :
    z.submodule ≤ p.submodule ⊔ q.submodule := by
  obtain ⟨hp,hq,h⟩ := h
  exact collision_center_on_line z ⟨p,hp⟩ ⟨q,hq⟩ hpq h

lemma collision_centers_card [Finite K] [Fintype (Projectivization K V)]
    (p q : Projectivization K V) (hpq : p ≠ q) :
    (univ.filter (fun z => Collides z p q)).card ≤ Nat.card K+1 := by
  have hh := card_le_card (show univ.filter (fun z => Collides z p q) ⊆
      univ.filter (fun z => z.submodule ≤ p.submodule ⊔ q.submodule) from by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _,collides_on_line z p q hpq (mem_filter.mp hz).2⟩)
  have he := joining_line_card p q hpq
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at he
  exact hh.trans_eq he

theorem collision_total [Finite K] [Fintype (Projectivization K V)]
    (A : Finset (Projectivization K V)) :
    ∑ z, orderedCollisions A z ≤ A.card*(A.card-1)*(Nat.card K+1) := by
  unfold orderedCollisions
  simp only [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ pq ∈ A.offDiag, (Nat.card K+1) := by
      apply sum_le_sum
      rintro ⟨p,q⟩ hpq
      have hh := collision_centers_card p q (mem_offDiag.mp hpq).2.2
      simpa only [card_eq_sum_ones,sum_filter] using hh
    _ = _ := by simp [offDiag_card,Nat.mul_sub_left_distrib]

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteImage
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

theorem card_le_image_add_collisions (s : Finset α) (f : α → β) :
    s.card ≤ (s.image f).card+(s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card := by
  let r : (s.image f) → α := fun b => (mem_image.mp b.property).choose
  have hr (b : s.image f) : r b ∈ s ∧ f (r b) = b.val :=
    (mem_image.mp b.property).choose_spec
  let D : Finset α := (s.image f).attach.image r
  let R := s \ D
  let g (a : α) : α := if h : a ∈ s then r ⟨f a,mem_image_of_mem f h⟩ else a
  have hg (a : α) (ha : a ∈ s) : g a ∈ D ∧ g a ∈ s ∧ f (g a) = f a := by
    dsimp only [g]
    rw [dite_eq_left ha]
    exact ⟨mem_image.mpr ⟨⟨f a,mem_image_of_mem f ha⟩,mem_attach _ _,rfl⟩,
      hr ⟨f a,mem_image_of_mem f ha⟩⟩
  have hR : R.card ≤ (s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card := by
    apply card_le_card_of_injOn (fun a => (a,g a))
    · intro a ha
      obtain ⟨ha,hn⟩ := mem_sdiff.mp ha
      obtain ⟨hgd,hgs,hgf⟩ := hg a ha
      have hne : a ≠ g a := by
        intro he
        exact hn (he.symm ▸ hgd)
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨ha,hgs,hne⟩,hgf.symm⟩
    · intro a ha b hb he
      exact congrArg Prod.fst he
  have hD : D.card ≤ (s.image f).card := by
    exact (card_image_le).trans_eq card_attach
  calc
    s.card ≤ (D ∪ R).card := card_le_card (by
      intro a ha
      by_cases hd : a ∈ D
      · exact mem_union_left _ hd
      · exact mem_union_right _ (mem_sdiff.mpr ⟨ha,hd⟩))
    _ ≤ D.card+R.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add hD hR

end
end SharpLogRamsey.FiniteImage

namespace SharpLogRamsey.Projection
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma noncentral_collision_le (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    ((A.subtype (· ≠ z)).offDiag.filter (fun pq => project z pq.1 = project z pq.2)).card ≤
      orderedCollisions A z := by
  apply card_le_card_of_injOn (fun pq => (pq.1.val,pq.2.val))
  · intro pq hpq
    obtain ⟨hm,he⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq,hne⟩ := mem_offDiag.mp hm
    apply mem_filter.mpr
    refine ⟨mem_offDiag.mpr ⟨mem_subtype.mp hp,mem_subtype.mp hq,?_⟩,?_⟩
    · exact fun h => hne (Subtype.ext h)
    · exact ⟨pq.1.property,pq.2.property,he⟩
  · intro p hp q hq he
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

theorem projection_loss (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    A.card ≤ (projected A z).card+orderedCollisions A z+1 := by
  have h := FiniteImage.card_le_image_add_collisions (A.subtype (· ≠ z)) (project z)
  have hcol := noncentral_collision_le A z
  have ha : A.card ≤ (A.subtype (· ≠ z)).card+1 := by
    rw [card_subtype]
    have hcount := card_filter_add_card_filter_not (s := A) (p := fun p => p = z)
    have hle : (A.filter (fun p => p = z)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
    simpa only [not_not] using (show A.card ≤ (A.filter (fun p => ¬p = z)).card+1 by omega)
  dsimp only [projected]
  omega

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteImage
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

lemma collisions_fiber_sum (s : Finset α) (f : α → β) :
    collisions s f = ∑ b ∈ s.image f,
      (s.filter (fun a => f a=b)).card*((s.filter (fun a => f a=b)).card-1) := by
  let E := s.offDiag.filter (fun ab => f ab.1 = f ab.2)
  have h : E.card = ∑ b ∈ s.image f, (E.filter (fun ab => f ab.1=b)).card :=
    card_eq_sum_card_fiberwise (f := fun ab => f ab.1) (fun ab hab =>
      mem_image_of_mem f (mem_offDiag.mp (mem_filter.mp hab).1).1)
  change E.card = _
  rw [h]
  apply sum_congr rfl
  intro b hb
  have he : E.filter (fun ab => f ab.1=b) = (s.filter (fun a => f a=b)).offDiag := by
    ext ab
    simp only [E,mem_filter,mem_offDiag]
    aesop
  rw [he,offDiag_card]
  simp [Nat.mul_sub_left_distrib]

lemma image_excess_sq (s : Finset α) (f : α → β) :
    ((s.card:ℝ)-(s.image f).card)^2 ≤ (s.image f).card*collisions s f := by
  let k (b : β) : ℝ := (s.filter (fun a => f a=b)).card
  have hk (b : β) (hb : b ∈ s.image f) : 1 ≤ k b := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    have : 0 < (s.filter (fun x => f x=f a)).card :=
      card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
    dsimp [k]
    exact_mod_cast this
  have hs : ∑ b ∈ s.image f, k b = s.card := by
    simp only [k,← Nat.cast_sum]
    congr 1
    exact (card_eq_sum_card_fiberwise (f := f) (fun a ha => mem_image_of_mem f ha)).symm
  have hc : ∑ b ∈ s.image f, k b*(k b-1) = (collisions s f:ℝ) := by
    rw [collisions_fiber_sum,Nat.cast_sum]
    apply sum_congr rfl
    intro b hb
    have hh : 1 ≤ (s.filter (fun a => f a=b)).card := by
      have hh := hk b hb
      dsimp only [k] at hh
      exact_mod_cast hh
    rw [Nat.cast_mul,Nat.cast_sub hh,Nat.cast_one]
  have hcs := sum_mul_sq_le_sq_mul_sq (s.image f) (fun _ => (1:ℝ)) (fun b => k b-1)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : ∑ b ∈ s.image f, (k b-1)^2 ≤ (collisions s f:ℝ) := by
    rw [← hc]
    apply sum_le_sum
    intro b hb
    nlinarith [hk b hb]
  have ht : ∑ b ∈ s.image f, (k b-1) = (s.card:ℝ)-(s.image f).card := by
    rw [sum_sub_distrib,hs]
    simp
  rw [ht] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem image_excess (s : Finset α) (f : α → β) :
    (s.card:ℝ) ≤ (s.image f).card+Real.sqrt ((s.image f).card*collisions s f) := by
  have h := image_excess_sq s f
  have hcard : ((s.image f).card:ℝ) ≤ s.card := by exact_mod_cast card_image_le (s:=s) (f:=f)
  have hh : (s.card:ℝ)-(s.image f).card ≤
      Real.sqrt ((s.image f).card*collisions s f) :=
    (Real.le_sqrt (sub_nonneg.mpr hcard) (by positivity)).mpr h
  linarith

lemma collisions_mono (s t : Finset α) (h : s ⊆ t) (f : α → β) :
    collisions s f ≤ collisions t f := by
  apply card_le_card
  intro ab hab
  obtain ⟨⟨ha,hb,hn⟩,he⟩ := by simpa only [mem_filter,mem_offDiag] using hab
  exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨h ha,h hb,hn⟩,he⟩

theorem cap_contraction (s : Finset α) (f : α → β) (W : Finset β) :
    ((s.filter (fun a => f a ∈ W)).card:ℝ) ≤
      W.card+Real.sqrt (W.card*collisions s f) := by
  let t := s.filter (fun a => f a ∈ W)
  have hi : t.image f ⊆ W := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    exact (mem_filter.mp ha).2
  have hic : ((t.image f).card:ℝ) ≤ W.card := by exact_mod_cast card_le_card hi
  have hc : (collisions t f:ℝ) ≤ collisions s f := by
    exact_mod_cast collisions_mono t s (filter_subset _ _) f
  exact (image_excess t f).trans (add_le_add hic
    (Real.sqrt_le_sqrt (mul_le_mul hic hc (by positivity) (by positivity))))

end
end SharpLogRamsey.FiniteImage
namespace SharpLogRamsey.Projection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma liftCap_card (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (liftCap A z W).card = ((A.subtype (· ≠ z)).filter (fun p => project z p ∈ W)).card :=
  card_image_of_injective _ Subtype.val_injective

lemma mem_liftCap (A : Finset (Projectivization K V)) (z p : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    p ∈ liftCap A z W ↔ p ∈ A ∧ ∃ hp : p ≠ z, project z ⟨p,hp⟩ ∈ W := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact ⟨mem_subtype.mp (mem_filter.mp ha).1,a.property,(mem_filter.mp ha).2⟩
  · rintro ⟨hp,hn,hw⟩
    exact mem_image.mpr ⟨⟨p,hn⟩,mem_filter.mpr ⟨mem_subtype.mpr hp,hw⟩,rfl⟩

lemma liftCap_subset (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) : liftCap A z W ⊆ A :=
  fun _ hp => ((mem_liftCap _ _ _ _).mp hp).1

theorem liftCap_contraction (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    ((liftCap A z W).card:ℝ) ≤ W.card+Real.sqrt (W.card*orderedCollisions A z) := by
  rw [liftCap_card]
  apply (FiniteImage.cap_contraction (A.subtype (· ≠ z)) (project z) W).trans
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast noncentral_collision_le A z

lemma fiber_on_line (z p q : Projectivization K V) (hp : p ≠ z) (hq : q ≠ z)
    (he : project z ⟨p,hp⟩ = project z ⟨q,hq⟩) :
    q.submodule ≤ z.submodule ⊔ p.submodule := by
  by_cases hpq : p=q
  · subst q
    exact le_sup_right
  have hz := collision_center_on_line z ⟨p,hp⟩ ⟨q,hq⟩ hpq he
  have hsub : z.submodule ⊔ p.submodule ≤ p.submodule ⊔ q.submodule :=
    sup_le hz le_sup_left
  have hEq : z.submodule ⊔ p.submodule = p.submodule ⊔ q.submodule := by
    apply Submodule.eq_of_le_of_finrank_eq hsub
    rw [joining_line_finrank z p hp.symm,joining_line_finrank p q hpq]
  rw [hEq]
  exact le_sup_right

variable [Finite K] [Fintype (Projectivization K V)]

lemma project_fiber_card (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (b : Projectivization K (V ⧸ z.submodule)) :
    ((A.subtype (· ≠ z)).filter (fun p => project z p=b)).card ≤ Nat.card K := by
  let F := (A.subtype (· ≠ z)).filter (fun p => project z p=b)
  by_cases hf : F.Nonempty
  · obtain ⟨p,hp⟩ := hf
    let L : Finset (Projectivization K V) :=
      univ.filter (fun q => q.submodule ≤ z.submodule ⊔ p.val.submodule)
    have hL : L.card = Nat.card K+1 := by
      have h := joining_line_card z p.val p.property.symm
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
      exact h
    have hz : z ∈ L := mem_filter.mpr ⟨mem_univ _,le_sup_left⟩
    have hb : F.card ≤ (L.erase z).card := by
      apply card_le_card_of_injOn Subtype.val
      · intro q hq
        apply mem_erase.mpr
        refine ⟨q.property,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
        exact fiber_on_line z p.val q.val p.property q.property
          ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
      · intro x hx y hy he
        exact Subtype.ext he
    rw [card_erase_of_mem hz,hL] at hb
    simpa using hb
  · have : F=∅ := not_nonempty_iff_eq_empty.mp hf
    change F.card ≤ _
    simp [this]

theorem liftCap_initial (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (liftCap A z W).card ≤ Nat.card K*W.card := by
  rw [liftCap_card]
  apply card_le_mul_card_image_of_maps_to (f := project z)
    (fun p hp => (mem_filter.mp hp).2) (Nat.card K)
  intro b hb
  apply le_trans _ (project_fiber_card A z b)
  apply card_le_card
  intro p hp
  obtain ⟨hp,he⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1,he⟩

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionCapture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma projected_liftCap (S : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    projected (liftCap S z W) z=projected S z∩W := by
  ext b
  constructor
  · intro hb
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hb
    have hh := (mem_liftCap S z p.val W).mp (mem_subtype.mp hp)
    obtain ⟨hS,hn,hW⟩ := hh
    exact mem_inter.mpr ⟨mem_image.mpr ⟨p,mem_subtype.mpr hS,rfl⟩,hW⟩
  · intro hb
    obtain ⟨hs,hw⟩ := mem_inter.mp hb
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hs
    exact mem_image.mpr ⟨p,mem_subtype.mpr ((mem_liftCap _ _ _ _).mpr
      ⟨mem_subtype.mp hp,p.property,hw⟩),rfl⟩

lemma projected_card_le (S : Finset (Projectivization K V)) (z : Projectivization K V) :
    (projected S z).card≤S.card := by
  exact card_image_le.trans (by rw [card_subtype]; exact card_filter_le _ _)

lemma inter_liftCap (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    S∩liftCap U z W=liftCap S z W := by
  ext p
  simp only [mem_inter,mem_liftCap]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hSU h.1,h.2⟩⟩

theorem original_support_loss (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (S\liftCap U z W).card ≤ (projected S z\W).card+orderedCollisions S z+1 := by
  have hc := projected_card_le (liftCap S z W) z
  rw [projected_liftCap] at hc
  have he : (S\liftCap U z W).card+(S∩liftCap U z W).card=S.card :=
    card_sdiff_add_card_inter S (liftCap U z W)
  rw [inter_liftCap S U hSU] at he
  have hi : (projected S z\W).card+(projected S z∩W).card=(projected S z).card :=
    card_sdiff_add_card_inter _ _
  have hp := projection_loss S z
  omega

theorem original_support_loss_real (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule)))
    (ε δ : ℝ) (hε : 0≤ε)
    (hcap : (projected S z\W).card≤ε*(projected S z).card)
    (hcol : (orderedCollisions S z:ℝ)+1≤δ*S.card) :
    ((S\liftCap U z W).card:ℝ)≤(ε+δ)*S.card := by
  have h := original_support_loss S U hSU z W
  have hr : ((S\liftCap U z W).card:ℝ)≤(projected S z\W).card+orderedCollisions S z+1 := by
    exact_mod_cast h
  have hp : ((projected S z).card:ℝ)≤S.card := by exact_mod_cast projected_card_le S z
  have hpc := mul_le_mul_of_nonneg_left hp hε
  linarith

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
open SharpLogRamsey.ScaleSelection SharpLogRamsey.MomentBudgetBridge

lemma beta_pos {η : ℝ} (hη : 0 < η) : 0 < beta η := by
  unfold beta
  positivity

lemma exponent_gap {η : ℝ} (hη : 0 < η) : 1-η/2+9*beta η < 1 := by
  unfold beta
  linarith

lemma scale_bounds {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0 < η)
    (h : Admissible σ η D R) :
    σ^(9*beta η) ≤ scaleL σ η D ∧
    σ^(10*beta η) ≤ scaleP σ η D R ∧
    scaleP σ η D R ≤ 4*σ^(1-η/2+9*beta η) := by
  have hσ0 : 0 < σ := by linarith
  have hb : 0 < beta η := beta_pos hη
  have hpow : 1 ≤ σ^beta η := Real.one_le_rpow hσ hb.le
  have hD0 : 0 ≤ D := (Real.rpow_nonneg hσ0.le _).trans h.D_lower
  have hL : σ^(9*beta η) ≤ scaleL σ η D := by
    calc
      _ = σ^beta η*σ^(8*beta η) := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.D_lower (Real.rpow_nonneg hσ0.le _)
  refine ⟨hL, ?_, ?_⟩
  · calc
      _ = σ^(9*beta η)*σ^beta η := by rw [← Real.rpow_add hσ0]; congr 1; ring
      _ ≤ scaleL σ η D*(R : ℝ) := mul_le_mul hL h.R_lower
        (Real.rpow_nonneg hσ0.le _) (by unfold scaleL; positivity)
      _ = _ := rfl
  · have hR : (R : ℝ) ≤ 4*σ^beta η := by linarith [h.R_upper]
    calc
      _ ≤ (σ^(1-η/2)*σ^(8*beta η))*(4*σ^beta η) := by
        unfold scaleP scaleL
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.D_upper
          (Real.rpow_nonneg hσ0.le _)) hR (Nat.cast_nonneg _) (by positivity)
      _ = 4*σ^(1-η/2+9*beta η) := by
        rw [mul_assoc, mul_left_comm (σ^(8*beta η)) 4, ← mul_assoc,
          mul_comm (σ^(1-η/2)) 4, mul_assoc, ← Real.rpow_add hσ0,
          ← Real.rpow_add hσ0]
        congr 2
        ring

lemma eventually_monomial_le_linear (C a ε : ℝ) (ha : a < 1) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^a ≤ ε*x := by
  have ht : Tendsto (fun x : ℝ => C*x^(a-1)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).const_mul C using 1 <;> simp
  filter_upwards [ht.eventually (gt_mem_nhds hε), eventually_gt_atTop (0 : ℝ)] with x hx hx0
  calc
    _ = (C*x^(a-1))*x := by
      have hp : x^(a-1)*x = x^a := by
        calc
          _ = x^(a-1)*x^(1 : ℝ) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring
      rw [mul_assoc, hp]
    _ ≤ ε*x := mul_le_mul_of_nonneg_right hx.le hx0.le

theorem eventually_P_le_linear {η : ℝ} (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      scaleP σ η D R ≤ ε*σ := by
  filter_upwards [eventually_monomial_le_linear 4 (1-η/2+9*beta η) ε
    (exponent_gap hη) hε, eventually_ge_atTop (1 : ℝ)] with σ hσ hσ1 D R h
  exact (scale_bounds hσ1 hη h).2.2.trans hσ

end SharpLogRamsey.SourceScales
end

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceScaleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma Kstar_eq (σ η D : ℝ) (hσ : 0<σ) :
    scaleKstar σ η D=scaleL σ η D*σ^(-2*beta η) := by
  unfold scaleKstar scaleL
  rw [mul_assoc,←Real.rpow_add hσ]
  congr 2
  ring

lemma R_bound {σ η D : ℝ} {R : ℕ} (hσ : 1 ≤ σ) (hη : 0<η)
    (h : Admissible σ η D R) : (R:ℝ) ≤ 4*σ^beta η := by
  have hh := Real.one_le_rpow hσ (beta_pos hη).le
  linarith [h.R_upper]

lemma L_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleL σ η D := by
  have hD : 0<D := (Real.rpow_pos_of_pos hσ _).trans_le h.D_lower
  unfold scaleL
  positivity

lemma P_pos {σ η D : ℝ} {R : ℕ} (hσ : 0<σ) (h : Admissible σ η D R) :
    0 < scaleP σ η D R := by
  have hR : (0:ℝ)<R := (Real.rpow_pos_of_pos hσ _).trans_le h.R_lower
  exact mul_pos (L_pos hσ h) hR

theorem eventually_sparse_loss {η : ℝ} (hη : 0<η) (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (D : ℝ) (R : ℕ), Admissible σ η D R →
      ∀ b τ : ℝ, b ≤ C*scaleKstar σ η D → τ ≤ C*σ^(-100*beta η) →
      b+scaleP σ η D R*τ ≤ δ*scaleL σ η D := by
  have hb := beta_pos hη
  have h1 : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<2*beta η by positivity)).const_mul C using 1 <;> simp [neg_mul]
  have h2 : Tendsto (fun σ : ℝ => 4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (show 0<99*beta η by positivity)).const_mul (4*C) using 1 <;> simp [neg_mul]
  have ht : Tendsto (fun σ : ℝ => C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) atTop (𝓝 0) := by
    simpa using h1.add h2
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1:ℝ)] with σ he hσ D R had b τ hb' hτ
  have hσ0 : 0<σ := by linarith
  have hL := (L_pos hσ0 had).le
  have hP := (P_pos hσ0 had).le
  have hR := R_bound hσ hη had
  have hh : (R:ℝ)*(C*σ^(-100*beta η)) ≤ 4*C*σ^(-99*beta η) := by
    calc
      _  ≤  (4*σ^beta η)*(C*σ^(-100*beta η)) :=
        mul_le_mul_of_nonneg_right hR (by positivity)
      _ = _ := by
        rw [show (4*σ^beta η)*(C*σ^(-100*beta η))=4*C*(σ^beta η*σ^(-100*beta η)) by ring,
          ←Real.rpow_add hσ0]
        congr 2
        ring
  have hb'' : b ≤ scaleL σ η D*(C*σ^(-2*beta η)) := by
    rw [Kstar_eq σ η D hσ0] at hb'
    nlinarith only [hb']
  have hτ' : scaleP σ η D R*τ ≤ scaleL σ η D*(4*C*σ^(-99*beta η)) := by
    calc
      _  ≤  scaleP σ η D R*(C*σ^(-100*beta η)) := mul_le_mul_of_nonneg_left hτ hP
      _ = scaleL σ η D*((R:ℝ)*(C*σ^(-100*beta η))) := mul_assoc _ _ _
      _  ≤  _ := mul_le_mul_of_nonneg_left hh hL
  calc
    _  ≤  scaleL σ η D*(C*σ^(-2*beta η)+4*C*σ^(-99*beta η)) := by linarith
    _  ≤  scaleL σ η D*δ := mul_le_mul_of_nonneg_left he.le hL
    _ = _ := mul_comm _ _

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourcePencilScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

lemma eventually_uniform_L {η : ℝ} (hη : 0<η) {Q : ℝ→Prop}
    (hQ : ∀ᶠ L : ℝ in atTop,Q L) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → Q (scaleL σ η D) := by
  obtain ⟨a,ha⟩ := eventually_atTop.mp hQ
  have ht := (tendsto_rpow_atTop (show 0<9*beta η by have := beta_pos hη; positivity)).eventually
    (eventually_ge_atTop a)
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with σ hσ hσ1 D R had
  exact ha _ (hσ.trans (scale_bounds hσ1 hη had).1)

lemma eventually_uniform_R {η : ℝ} (hη : 0<η) (a : ℝ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R → a≤(R:ℝ) := by
  have ht := (tendsto_rpow_atTop (beta_pos hη)).eventually (eventually_ge_atTop a)
  filter_upwards [ht] with σ hσ D R had
  exact hσ.trans had.R_lower

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_SourceTrainingScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_training_loss {η : ℝ} (hη : 0<η) (C δ : ℝ)
    (hC : 0≤C) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      ∀ b τ : ℝ,b≤C*scaleKstar σ η D → τ≤C*σ^(-100*beta η) →
        b+2*scaleP σ η D R*τ≤δ*scaleL σ η D := by
  filter_upwards [eventually_sparse_loss hη (2*C) δ (by positivity) hδ,
    eventually_ge_atTop (1:ℝ)] with σ hh hσ D R had b τ hb hτ
  have hK : 0 ≤ scaleKstar σ η D := by
    rw [Kstar_eq _ _ _ (by linarith)]
    exact mul_nonneg (L_pos (by linarith) had).le (Real.rpow_nonneg (by linarith) _)
  have h1 : b≤(2*C)*scaleKstar σ η D := by nlinarith
  have h2 : 2*τ≤(2*C)*σ^(-100*beta η) := by linarith
  have hh' := hh D R had b (2*τ) h1 h2
  nlinarith only [hh']

end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Selection_UniversalTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Fintype Ω] in
lemma rows_card_le (n : ℕ) (z : Table Ω n) : (rows n z).card≤n := by
  induction n with
  | zero => simp [rows]
  | succ n ih => exact (card_insert_le _ _).trans (Nat.add_le_add_right (ih _) 1)

omit [Fintype Ω] in
lemma first_none_iff (A : Ω→Prop) (n : ℕ) (z : Table Ω n) :
    first A n z=none ↔ ∀ x∈rows n z,¬A x := by
  induction n with
  | zero => simp [first,rows]
  | succ n ih =>
    by_cases h : A z.1
    · simp [first,rows,h]
    · simpa [first,rows,h] using ih z.2

lemma missed_probability (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (∑ z,tableWeight p n z*(if first A n z=none then 1 else 0))=(1-acceptProb p A)^n := by
  have hh (z : Table Ω n) :
      (if first A n z=none then (1:ℝ) else 0)=1-outcome A (fun _ => 1) n z := by
    unfold outcome
    cases first A n z <;> simp
  simp_rw [hh,mul_sub,mul_one]
  rw [sum_sub_distrib,tableWeight_total]
  change 1-integral p A (fun _ => 1) n=_
  rw [production_probability]
  ring

lemma missing_exp (p : Law Ω) (A : Ω→Prop) (n : ℕ) :
    (1-acceptProb p A)^n≤exp (-(n:ℝ)*acceptProb p A) := by
  have hh : 1-acceptProb p A≤exp (-acceptProb p A) := by
    have := add_one_le_exp (-acceptProb p A)
    linarith
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr (acceptProb_le_one p A)) hh n
  rw [←exp_nat_mul] at hp
  simpa only [mul_neg,neg_mul] using hp

theorem exists_universal (p : Law Ω) (A : ι→Ω→Prop) (n : ℕ)
    (h : (∑ i,(1-acceptProb p (A i))^n)<1) :
    ∃ z : Table Ω n,∀ i,∃ x∈rows n z,A i x := by
  by_contra! hn
  have hl (z : Table Ω n) :
      (1:ℝ)≤∑ i,if first (A i) n z=none then 1 else 0 := by
    obtain ⟨i,hi⟩ := hn z
    have hm : first (A i) n z=none := (first_none_iff _ _ _).mpr hi
    have hh := single_le_sum (f := fun i => if first (A i) n z=none then (1:ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)
    simpa [hm] using hh
  have hh : (1:ℝ)≤∑ z,tableWeight p n z*(∑ i,if first (A i) n z=none then 1 else 0) := by
    calc
      _ = ∑ z,tableWeight p n z := (tableWeight_total p n).symm
      _ ≤ _ := by
        apply sum_le_sum
        intro z _
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hl z) (tableWeight_nonneg p n z)
  simp_rw [mul_sum] at hh
  rw [sum_comm] at hh
  simp_rw [missed_probability] at hh
  linarith

theorem exists_cover (p : Law Ω) (A : ι→Ω→Prop) (a H : ℝ)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i)) :
    ∃ r : Finset Ω,r.card≤⌈exp (2*a)⌉₊ ∧ (∀ i,∃ x∈r,A i x) ∧
      log ((⌈exp (2*a)⌉₊:ℝ)+1)≤2*a+log 3 := by
  let n := ⌈exp (2*a)⌉₊
  have hN : exp (2*a)≤(n:ℝ) := Nat.le_ceil _
  have hl : (∑ i,(1-acceptProb p (A i))^n)<1 := by
    calc
      _ ≤ (∑ _i : ι,exp (-(n:ℝ)*exp (-a))) := by
        apply sum_le_sum
        intro i _
        apply (missing_exp p (A i) n).trans
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg n : (0:ℝ)≤n)
        nlinarith only [hh]
      _ = (Fintype.card ι:ℝ)*exp (-(n:ℝ)*exp (-a)) := by simp
      _ ≤ exp H*exp (-(n:ℝ)*exp (-a)) := by gcongr
      _ = exp (H-(n:ℝ)*exp (-a)) := by rw [←exp_add]; congr 1; ring
      _ ≤ exp (-1) := by
        apply exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hN (exp_pos (-a)).le
        have he : exp (2*a)*exp (-a)=exp a := by rw [←exp_add]; congr 1; ring
        rw [he] at hh
        linarith
      _ < 1 := exp_lt_one_iff.mpr (by norm_num)
  obtain ⟨z,hz⟩ := exists_universal p A n hl
  refine ⟨rows n z,rows_card_le n z,hz,?_⟩
  have hn : (n:ℝ)<exp (2*a)+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have he : 1≤exp (2*a) := one_le_exp_iff.mpr (by linarith)
  have hnp : (0:ℝ)<(n:ℝ)+1 := by positivity
  calc
    _ ≤ log (3*exp (2*a)) := by apply log_le_log hnp; linarith
    _ = _ := by rw [log_mul (by norm_num) (exp_ne_zero _),log_exp]; ring

end
end SharpLogRamsey.PublicTables

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_ValidationCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma coverInput_card (W : Finset (Projectivization K V))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ) (C b : ℝ) :
    (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      exp (((Fintype.card (Projectivization K V):ℝ)+
        Fintype.card (Projectivization K (Module.Dual K V)))*log 2) := by
  have hc := Fintype.card_subtype_le (CoverInput W U N t C b)
  have hc' : (Fintype.card {z // CoverInput W U N t C b z}:ℝ) ≤
      (2:ℝ)^Fintype.card (Projectivization K V)*
      (2:ℝ)^Fintype.card (Projectivization K (Module.Dual K V)) := by
    simpa only [Fintype.card_prod,Fintype.card_finset,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (show (Fintype.card {x // CoverInput W U N t C b x}:ℝ) ≤ Fintype.card (Finset (Projectivization K V) × Finset (Projectivization K (Module.Dual K V))) by exact_mod_cast hc)
  apply hc'.trans_eq
  rw [add_mul,exp_add,exp_nat_mul,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma row_ratio_exp {x w b : ℝ} (_hx : 0<x) (hw : 0<w)
    (h : w ≤ exp b*x) (hrow : ℕ) : exp (-((hrow:ℝ)*b)) ≤ (x/w)^hrow := by
  have hh : exp (-b) ≤ x/w := by
    rw [le_div_iff₀ hw,exp_neg]
    apply (inv_mul_le_iff₀ (exp_pos b)).mpr
    nlinarith only [h]
  have hh' := pow_le_pow_left₀ (exp_pos (-b)).le hh hrow
  rwa [←exp_nat_mul, mul_neg] at hh'

theorem public_validation_cover {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : Finset (Projectivization K V)) (hW : W.Nonempty)
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t ≤ U.card)
    (C b : ℝ) (hC : 1 ≤ C) (hb : 0 ≤ b)
    (hprod : (N:ℝ)*t ≤ 2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let M := 1000*C*q^(n+3)/N
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let a := (h:ℝ)*b+log 2+log (H+1)
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E ∈ caps, E ⊆ U ∧ (E.card:ℝ) ≤ M) ∧
      (∀ z, CoverInput W U N t C b z →
        ∃ E ∈ caps, (99/100:ℝ)*t ≤ (z.2∩E).card) ∧
      log ((caps.card:ℝ)+1) ≤ 2*a+log 3 := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let M := 1000*C*q^(n+3)/N
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let a := (h:ℝ)*b+log 2+log (H+1)
  have hq : 0<q := by change 0<(Nat.card K:ℝ); exact_mod_cast Nat.card_pos (α:=K)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have htr : (0:ℝ)<t := by exact_mod_cast ht
  have hw : (0:ℝ)<W.card := by exact_mod_cast card_pos.mpr hW
  have hut : (t:ℝ) ≤ U.card := by exact_mod_cast htu
  have hh : 0<h := scheduleLength_pos hq htr hut
  have hM : 0<M := by
    dsimp [M]
    have : 0<C := by linarith
    positivity
  have hH : 0 ≤ H := by dsimp [H]; exact mul_nonneg (by positivity) (log_nonneg (by norm_num))
  have ha₀ : 0 ≤ (h:ℝ)*b+log 2 := by positivity
  have hHP : 0 < H+1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; exact add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1 ≤ exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left hHP.le (one_le_exp_iff.mpr ha₀)
  let ι := {z // CoverInput W U N t C b z}
  let A : ι → (Fin h → Projectivization K V) → Prop := fun i =>
    implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M)
  have hprob : ∀ i, exp (-a) ≤ PublicTables.acceptProb (rowLaw W hW h) (A i) := by
    intro i
    obtain ⟨hx,hxw,hcap,hratio,htu',hct,hsp⟩ := i.2
    have hxr : (0:ℝ) < i.1.1.card := by exact_mod_cast card_pos.mpr hx
    have htt : i.1.2.Nonempty := card_pos.mp (by omega)
    have hsize := scheduleLength_size hq htr hut hNr hxr hC hcap hprod
      (pow_nonneg hq.le (n+3))
    have hsp' : (∑ y∈i.1.2,∑ x∈univ.filter (fun x => SharpLogRamsey.Incidence.Incident x y),uniformMass i.1.1 x) ≤
        (i.1.2.card:ℝ)/(10000*q) := by
      rw [uniform_incidence_sum]
      apply (div_le_iff₀ hxr).mpr
      apply hsp.trans_eq
      dsimp [q]
      ring
    have hg := projective_ideal_acceptance hdim i.1.1 hx U i.1.2 htt h hh M hM hsize hsp'
    change _ ≤ PublicTables.acceptProb (rowLaw W hW h)
      (implementAccept i.1.1 (GoodCap SharpLogRamsey.Incidence.Incident q U i.1.2 M))
    rw [proposal_acceptance _ _ hx hW hxw]
    have hr := row_ratio_exp hxr hw hratio h
    have hprod' := mul_le_mul hr hg (by norm_num : (0:ℝ) ≤ 9/10) (by positivity)
    apply le_trans _ hprod'
    have he : exp (-((h:ℝ)*b+log 2))= exp (-((h:ℝ)*b))/2 := by
      rw [neg_add,exp_add,exp_neg (log 2),exp_log (by norm_num : (0:ℝ)<2)]
      ring
    calc
      exp (-a) ≤ exp (-((h:ℝ)*b+log 2)) := by
        apply exp_le_exp.mpr
        have hh' : 0 ≤ log (H+1) := log_nonneg (by linarith)
        dsimp [a]; linarith
      _ ≤ _ := by rw [he]; nlinarith [exp_pos (-((h:ℝ)*b))]
  obtain ⟨rows,hcard,hcovers,hlen⟩ := PublicTables.exists_cover (rowLaw W hW h) A a H ha
    (coverInput_card W U N t C b) hea hprob
  let goodrows := rows.filter (fun z => ((cap SharpLogRamsey.Incidence.Incident q U z).card:ℝ) ≤ M)
  let caps := goodrows.image (cap SharpLogRamsey.Incidence.Incident q U)
  refine ⟨caps,?_,?_,?_⟩
  · intro E hE
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hE
    exact ⟨filter_subset _ _,(mem_filter.mp hz).2⟩
  · intro z hz
    obtain ⟨r,hr,hacc⟩ := hcovers ⟨z,hz⟩
    have hg : GoodCap SharpLogRamsey.Incidence.Incident q U z.2 M r := hacc.2
    refine ⟨cap SharpLogRamsey.Incidence.Incident q U r,mem_image.mpr ⟨r,mem_filter.mpr ⟨hr,hg.1⟩,rfl⟩,?_⟩
    have hc := cap_capture hz.2.2.2.2.1 hg
    rw [hz.2.2.2.2.2.1] at hc
    nlinarith only [hc]
  · have hc : caps.card ≤ ⌈exp (2*a)⌉₊ :=
      (card_image_le.trans (card_filter_le _ _)).trans hcard
    apply le_trans _ hlen
    apply log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hc 1

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectiveTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ProjectiveDuality
open Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

variable [FiniteDimensional K V]

lemma pullback_cover {α β : Type*} (e : α ≃ β) (U S : Finset α)
    (E : Finset β) (hE : E ⊆ U.image e) :
    E.image e.symm ⊆ U ∧ (E.image e.symm).card=E.card ∧
      (S∩E.image e.symm).card=((S.image e)∩E).card := by
  refine ⟨?_,card_image_of_injective _ e.symm.injective,?_⟩
  · intro a ha
    obtain ⟨b,hb,he⟩ := mem_image.mp ha
    obtain ⟨a₀,ha₀,he₀⟩ := mem_image.mp (hE hb)
    have hba : e.symm b=a₀ := by rw [←he₀,e.symm_apply_apply]
    rw [←he,hba]
    exact ha₀
  · have he : (S∩E.image e.symm).image e=(S.image e)∩E := by
      rw [image_inter _ _ e.injective]
      congr 1
      ext b
      simp
    rw [←he,card_image_of_injective _ e.injective]

end
end SharpLogRamsey.ProjectiveDuality

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionCenterTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence SharpLogRamsey.ProjectiveDuality Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma cut_card_sum {n : ℕ} (hdim : Module.finrank K V = n+3)
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z, (cut T z).card = (∑ i ∈ range (n+2), Nat.card K^i)*T.card := by
  simp only [cut,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  have hh (t : Projectivization K (Module.Dual K V)) :
      (∑ z : Projectivization K V, if SharpLogRamsey.Incidence.Incident z t then 1 else 0) =
        ∑ i ∈ range (n+2), Nat.card K^i := by
    have h := _root_.OAI.SharpLogRamsey.Incidence.card_incident_points (d := n+2) hdim t
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
    simpa only [card_eq_sum_ones,sum_filter] using h
  simp_rw [hh]
  simp [mul_comm]

omit [Fintype (Projectivization K (Module.Dual K V))] in
lemma surviving_incidence_sum {n : ℕ} (hdim : Module.finrank K V = n+3)
    (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z, incidenceCount S (cut T z) =
      (∑ i ∈ range (n+2), Nat.card K^i)*incidenceCount S T := by
  simp only [incidenceCount,cut,sum_filter]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro t ht
  have hh (a : ℕ) : (∑ z : Projectivization K V, if SharpLogRamsey.Incidence.Incident z t then a else 0) =
      (∑ i ∈ range (n+2), Nat.card K^i)*a := by
    have h := _root_.OAI.SharpLogRamsey.Incidence.card_incident_points (d := n+2) hdim t
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
    rw [← sum_filter]
    simp [h]
  exact hh _

attribute [local instance] OAI.SharpLogRamsey.Projection.flat_JoinedProjectionCenterTools_1
lemma cut_variance {n : ℕ} (hdim : Module.finrank K V = n+3)
    (T : Finset (Projectivization K (Module.Dual K V))) :
    ∑ z : Projectivization K V,
      ((cut T z).card-(∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)/
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i)*T.card)^2 ≤
          (Nat.card K:ℝ)^(n+1)*T.card := by
  let w : Projectivization K (Module.Dual K V) → ℝ := fun t => if t ∈ T then 1 else 0
  have hw : (∑ t, w t) = (T.card:ℝ) := by simp [w]
  have hw2 : (∑ t, w t^2) = (T.card:ℝ) := by simp [w]
  have hv := projective_variance_le
    (show Module.finrank K (Module.Dual K V) = n+3 from Subspace.dual_finrank_eq.trans hdim) w
  rw [hw,hw2,← (bidual (K:=K) (V:=V)).sum_comp] at hv
  have hcut (z : Projectivization K V) :
      weightedIncidences SharpLogRamsey.Incidence.Incident w (bidual z) = ((cut T z).card:ℝ) := by
    simp only [weightedIncidences,incident_bidual,w]
    rw [← sum_filter,← sum_filter]
    simp only [sum_const,nsmul_eq_mul,mul_one]
    congr 2
    ext t
    simp [cut,and_comm]
  simp_rw [hcut] at hv
  exact hv

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteAveraging
open Finset
open scoped BigOperators

lemma exists_small {α : Type*} [Fintype α] (f : α → ℝ)
    (h : ∑ x, f x < Fintype.card α) : ∃ x, f x < 1 := by
  by_contra hn
  push Not at hn
  have hh : (Fintype.card α:ℝ) ≤ ∑ x, f x := by
    simpa using sum_le_sum (s := univ) (f := fun _ => (1:ℝ)) (g := f) (fun x _ => hn x)
  exact not_lt_of_ge hh h

lemma exists_five {α : Type*} [Fintype α] (f₁ f₂ f₃ f₄ f₅ : α → ℝ)
    (hf₁ : ∀ x, 0 ≤ f₁ x) (hf₂ : ∀ x, 0 ≤ f₂ x) (hf₃ : ∀ x, 0 ≤ f₃ x)
    (hf₄ : ∀ x, 0 ≤ f₄ x) (hf₅ : ∀ x, 0 ≤ f₅ x)
    (h : (∑ x, f₁ x)+(∑ x, f₂ x)+(∑ x, f₃ x)+(∑ x, f₄ x)+(∑ x, f₅ x) <
      Fintype.card α) :
    ∃ x, f₁ x < 1 ∧ f₂ x < 1 ∧ f₃ x < 1 ∧ f₄ x < 1 ∧ f₅ x < 1 := by
  have hs : ∑ x, (f₁ x+f₂ x+f₃ x+f₄ x+f₅ x) < (Fintype.card α:ℝ) := by
    simpa only [sum_add_distrib] using h
  obtain ⟨x,hx⟩ := exists_small _ hs
  exact ⟨x,by linarith [hf₂ x,hf₃ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₃ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₄ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₃ x,hf₅ x],
    by linarith [hf₁ x,hf₂ x,hf₃ x,hf₄ x]⟩

end SharpLogRamsey.FiniteAveraging

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem exists_center {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (δ u cS cA e : ℝ) (hδ : 0<δ) (hu : 0<u) (hcS : 0 < cS) (hcA : 0 < cA) (he : 0<e)
    (hbudget :
      (Nat.card K:ℝ)^(n+1)*T.card/δ^2+
      (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)*U.card/u+
      ((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ)/cS+
      ((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ)/cA+
      (∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)*incidenceCount S T/e <
        ∑ i ∈ range (n+3), (Nat.card K:ℝ)^i) :
    ∃ z : Projectivization K V,
      |((cut T z).card:ℝ)-(∑ i ∈ range (n+2), (Nat.card K:ℝ)^i)/
        (∑ i ∈ range (n+3), (Nat.card K:ℝ)^i)*T.card| < δ ∧
      ((cut U z).card:ℝ)<u ∧ (orderedCollisions S z:ℝ) < cS ∧
      (orderedCollisions A z:ℝ) < cA ∧ (incidenceCount S (cut T z):ℝ)<e := by
  let Q : ℝ := ∑ i ∈ range (n+3), (Nat.card K:ℝ)^i
  let H : ℝ := ∑ i ∈ range (n+2), (Nat.card K:ℝ)^i
  let v (z : Projectivization K V) : ℝ := ((cut T z).card-H/Q*T.card)^2/δ^2
  let a (z : Projectivization K V) : ℝ := (cut U z).card/u
  let b (z : Projectivization K V) : ℝ := orderedCollisions S z/cS
  let c (z : Projectivization K V) : ℝ := orderedCollisions A z/cA
  let f (z : Projectivization K V) : ℝ := incidenceCount S (cut T z)/e
  have hv : ∑ z, v z ≤ (Nat.card K:ℝ)^(n+1)*T.card/δ^2 := by
    simp only [v,← sum_div]
    exact div_le_div_of_nonneg_right (cut_variance hdim T) (sq_nonneg δ)
  have ha : ∑ z, a z = H*U.card/u := by
    simp only [a,← sum_div,← Nat.cast_sum]
    rw [cut_card_sum hdim]
    simp [H]
  have hb : ∑ z, b z ≤ ((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ)/cS := by
    simp only [b,← sum_div,← Nat.cast_sum]
    exact div_le_div_of_nonneg_right (by exact_mod_cast collision_total S) hcS.le
  have hc : ∑ z, c z ≤ ((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ)/cA := by
    simp only [c,← sum_div,← Nat.cast_sum]
    exact div_le_div_of_nonneg_right (by exact_mod_cast collision_total A) hcA.le
  have hf : ∑ z, f z = H*incidenceCount S T/e := by
    simp only [f,← sum_div,← Nat.cast_sum]
    rw [surviving_incidence_sum hdim]
    simp [H]
  have hQ : (Fintype.card (Projectivization K V):ℝ) = Q := by
    rw [← Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
    simp [Q]
  have hall : (∑ z, v z)+(∑ z, a z)+(∑ z, b z)+(∑ z, c z)+(∑ z, f z) <
      Fintype.card (Projectivization K V) := by
    rw [ha,hf,hQ]
    exact lt_of_le_of_lt (by linarith) hbudget
  obtain ⟨z,hz₁,hz₂,hz₃,hz₄,hz₅⟩ := FiniteAveraging.exists_five v a b c f
    (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun _ => div_nonneg (by positivity) hu.le)
    (fun _ => div_nonneg (by positivity) hcS.le)
    (fun _ => div_nonneg (by positivity) hcA.le)
    (fun _ => div_nonneg (by positivity) he.le) hall
  refine ⟨z,?_,(div_lt_one hu).mp hz₂,(div_lt_one hcS).mp hz₃,
    (div_lt_one hcA).mp hz₄,(div_lt_one he).mp hz₅⟩
  have hh := (div_lt_one (sq_pos_of_pos hδ)).mp hz₁
  exact (sq_lt_sq₀ (abs_nonneg _) hδ.le).mp (by simpa [v,sq_abs] using hh)

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionCenterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma center_budget (q N Q H s a t u e τ : ℝ)
    (hq : 2≤q) (hN : 0<N) (hH : 0≤H) (hQ : q*N≤Q) (hHQ : q*H≤Q)
    (hs : 0 < s) (ha : 0<a) (hu : 0<u) (hτ : 0<τ)
    (hst : s≤N/100000) (htt : 1000000*q≤t) (he : e≤τ*s*t/q) :
    N*t/(t/(100*q))^2+H*u/(100*u/q)+s^2*(q+1)/(s/100)+
      a^2*(q+1)/(100*a^2/N)+H*e/(100*τ*s*t/q^2)<Q := by
  have hq0 : 0<q := by linarith
  have ht : 0<t := lt_of_lt_of_le (by positivity) htt
  have hQ0 : 0<Q := (mul_pos hq0 hN).trans_le hQ
  have hv : N*t/(t/(100*q))^2≤Q/100 := by
    calc
      _ = 10000*N*q^2/t := by field_simp; ring
      _ ≤ 10000*N*q^2/(1000000*q) := div_le_div_of_nonneg_left (by positivity) (by positivity) htt
      _ = q*N/100 := by field_simp; ring
      _ ≤ _ := by linarith only [hQ]
  have hd : H*u/(100*u/q)≤Q/100 := by
    calc
      _ = q*H/100 := by field_simp
      _ ≤ _ := by linarith only [hHQ]
  have hcS : s^2*(q+1)/(s/100)≤Q/500 := by
    calc
      _ = 100*s*(q+1) := by field_simp
      _ ≤ 200*s*q := by nlinarith
      _ ≤ q*N/500 := by nlinarith [mul_le_mul_of_nonneg_right hst hq0.le]
      _ ≤ _ := by linarith only [hQ]
  have hcA : a^2*(q+1)/(100*a^2/N)≤Q/50 := by
    calc
      _ = N*(q+1)/100 := by field_simp
      _ ≤ q*N/50 := by nlinarith
      _ ≤ _ := by linarith only [hQ]
  have hi : H*e/(100*τ*s*t/q^2)≤Q/100 := by
    calc
      _ ≤ H*(τ*s*t/q)/(100*τ*s*t/q^2) := by gcongr
      _ = q*H/100 := by field_simp
      _ ≤ _ := by linarith only [hHQ]
  linarith only [hv,hd,hcS,hcA,hi,hQ0]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.Projection.flat_JoinedProjectionCenterBounds_1
attribute [local instance] OAI.SharpLogRamsey.Projection.flat_JoinedProjectionCenterBounds_2
theorem good_center {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hA : A.Nonempty) (hU : U.Nonempty) (τ : ℝ) (hτ : 0<τ)
    (hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤τ*S.card*T.card/Nat.card K) :
    ∃ z : Projectivization K V,
      |((cut T z).card:ℝ)-(∑ i∈range (n+2),(Nat.card K:ℝ)^i)/
        (∑ i∈range (n+3),(Nat.card K:ℝ)^i)*T.card| < (T.card:ℝ)/(100*Nat.card K) ∧
      ((cut U z).card:ℝ)<100*U.card/Nat.card K ∧
      (orderedCollisions S z:ℝ)<(S.card:ℝ)/100 ∧
      (orderedCollisions A z:ℝ)<100*(A.card:ℝ)^2/(Nat.card K:ℝ)^(n+1) ∧
      (incidenceCount S (cut T z):ℝ)<100*τ*S.card*T.card/(Nat.card K:ℝ)^2 := by
  let q : ℝ := Nat.card K
  let N := q^(n+1)
  let H := ∑ i∈range (n+2),q^i
  let Q := ∑ i∈range (n+3),q^i
  have hq : 2≤q := by
    dsimp only [q]
    exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hq0 : 0<q := by linarith
  have hN : 0<N := by dsimp [N]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  have hHQ : q*H≤Q := by have hh := geom_sum_succ (x:=q) (n:=n+2); dsimp [H,Q]; linarith
  have hQ : q*N≤Q := by
    have hh : q^(n+2)≤Q := single_le_sum (fun i hi => by positivity) (by simp)
    simpa only [N,show n+2=(n+1)+1 by omega,pow_succ,mul_comm] using hh
  have hs : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have ha : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hA
  have hu : (0:ℝ)<U.card := by exact_mod_cast card_pos.mpr hU
  have ht : (0:ℝ)<T.card := lt_of_lt_of_le (by positivity) hlarge
  apply exists_center hdim S A T U ((T.card:ℝ)/(100*q)) (100*U.card/q)
    (S.card/100) (100*(A.card:ℝ)^2/N) (100*τ*S.card*T.card/q^2)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  have hnS : (((S.card*(S.card-1)*(Nat.card K+1):ℕ):ℝ))≤(S.card:ℝ)^2*(q+1) := by
    push_cast
    have hh : ((S.card-1:ℕ):ℝ)≤S.card := by exact_mod_cast Nat.sub_le S.card 1
    dsimp only [q]
    calc
      _ ≤ (S.card:ℝ)*(S.card:ℝ)*(Nat.card K+1) := by gcongr
      _ = _ := by ring
  have hnA : (((A.card*(A.card-1)*(Nat.card K+1):ℕ):ℝ))≤(A.card:ℝ)^2*(q+1) := by
    push_cast
    have hh : ((A.card-1:ℕ):ℝ)≤A.card := by exact_mod_cast Nat.sub_le A.card 1
    dsimp only [q]
    calc
      _ ≤ (A.card:ℝ)*(A.card:ℝ)*(Nat.card K+1) := by gcongr
      _ = _ := by ring
  have hb := center_budget q N Q H S.card A.card T.card U.card (incidenceCount S T) τ
    hq hN hH hQ hHQ hs ha hu hτ hsmall hlarge hsparse
  apply lt_of_le_of_lt _ hb
  dsimp only [N,H,Q,q]
  gcongr

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma quotientCut_card (T : Finset (Projectivization K (Module.Dual K V)))
    (z : Projectivization K V) : (quotientCut T z).card=(cut T z).card := by
  rw [quotientCut,card_image_of_injective _ (projectDual_injective z)]
  simp only [card_subtype,cut]

lemma quotientCut_mono {T U : Finset (Projectivization K (Module.Dual K V))}
    (h : T⊆U) (z : Projectivization K V) : quotientCut T z⊆quotientCut U z := by
  apply image_subset_image
  intro t ht
  exact mem_subtype.mpr (h (mem_subtype.mp ht))

lemma projected_mono {S U : Finset (Projectivization K V)} (h : S⊆U)
    (z : Projectivization K V) : projected S z⊆projected U z := by
  apply image_subset_image
  intro p hp
  exact mem_subtype.mpr (h (mem_subtype.mp hp))

lemma quotient_incidence_le (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (z : Projectivization K V) :
    incidenceCount (projected S z) (quotientCut T z)≤ incidenceCount S (cut T z) := by
  unfold incidenceCount quotientCut
  rw [sum_image (fun a ha b hb he => projectDual_injective z he)]
  have hrow (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
      ((projected S z).filter (fun p => SharpLogRamsey.Incidence.Incident p (projectDual z t))).card≤
        (S.filter (fun p => SharpLogRamsey.Incidence.Incident p t.val)).card := by
    unfold projected
    rw [filter_image]
    simp only [project_incident_iff]
    apply card_image_le.trans
    apply card_le_card_of_injOn (fun p : {p : Projectivization K V // p≠z} => p.val)
    · intro p hp
      exact mem_filter.mpr ⟨mem_subtype.mp (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
    · intro p hp r hr he
      exact Subtype.ext he
  apply (sum_le_sum (fun t ht => hrow t)).trans_eq
  have he : (T.subtype (SharpLogRamsey.Incidence.Incident z)).image Subtype.val=cut T z := by
    ext t
    simp [cut]
  rw [←he,sum_image (fun a ha b hb h => Subtype.ext h)]

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma cut_mean_bounds (q : ℝ) (hq : 2≤q) (n : ℕ) :
    1/(2*q) ≤ (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i) ∧
    (∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i) ≤ 1/q := by
  let H := ∑ i∈range (n+2),q^i
  let Q := ∑ i∈range (n+3),q^i
  have hH : 1≤H := by
    have hh := single_le_sum (s:=range (n+2)) (f:=fun i => q^i)
      (fun i hi => pow_nonneg (by linarith) i) (by simp : 0∈range (n+2))
    simpa only [pow_zero] using hh
  have he : Q=q*H+1 := geom_sum_succ
  have hq0 : 0<q := by linarith
  have hQ : 0<Q := by rw [he]; positivity
  constructor
  · apply (div_le_div_iff₀ (by positivity) hQ).mpr
    rw [he]
    have hh : 1≤q*H := by nlinarith
    nlinarith
  · apply (div_le_div_iff₀ hQ hq0).mpr
    rw [he]
    nlinarith

lemma actual_cut_bounds (q t x μ : ℝ) (hq : 0<q) (ht : 0≤t)
    (hμ : 1/(2*q)≤μ ∧ μ≤1/q) (hx : |x-μ*t|<t/(100*q)) :
    t/(3*q)≤x ∧ x≤2*t/q := by
  have he := abs_lt.mp hx
  have hlo := mul_le_mul_of_nonneg_right hμ.1 ht
  have hhi := mul_le_mul_of_nonneg_right hμ.2 ht
  constructor
  · have hh : t/(3*q)≤t/(2*q)-t/(100*q) := by
      field_simp
      nlinarith
    have hmul : 1/(2*q)*t=t/(2*q) := by ring
    rw [hmul] at hlo
    linarith
  · have hmul : 1/q*t=t/q := by ring
    rw [hmul] at hhi
    have hh : t/q+t/(100*q)≤2*t/q := by
      field_simp
      nlinarith
    linarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem quotient_data {n : ℕ} (hdim : Module.finrank K V=n+3)
    (S A : Finset (Projectivization K V))
    (T U : Finset (Projectivization K (Module.Dual K V)))
    (hA : A.Nonempty) (hTU : T⊆U) (τ : ℝ) (hτ : 0<τ)
    (hS : 100≤S.card)
    (hsmall : (S.card:ℝ)≤(Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T.card)
    (hsparse : (incidenceCount S T:ℝ)≤τ*S.card*T.card/Nat.card K) :
    ∃ z : Projectivization K V,
      (9/10:ℝ)*S.card≤(projected S z).card ∧
      (T.card:ℝ)/(3*Nat.card K)≤(quotientCut T z).card ∧
      ((quotientCut T z).card:ℝ)≤2*T.card/Nat.card K ∧
      ((quotientCut U z).card:ℝ)≤100*U.card/Nat.card K ∧
      (S.card:ℝ)*T.card/(4*Nat.card K)≤
        (projected S z).card*(quotientCut T z).card ∧
      (incidenceCount (projected S z) (quotientCut T z):ℝ)≤
        400*τ*(projected S z).card*(quotientCut T z).card/Nat.card K ∧
      (orderedCollisions S z:ℝ)<(S.card:ℝ)/100 ∧
      (orderedCollisions A z:ℝ)<100*(A.card:ℝ)^2/(Nat.card K:ℝ)^(n+1) := by
  let q : ℝ := Nat.card K
  have hq : 2≤q := by dsimp [q]; exact_mod_cast (show 2≤Nat.card K from Finite.one_lt_card)
  have hq0 : 0<q := by linarith
  have ht : (0:ℝ)<T.card := lt_of_lt_of_le (by positivity) hlarge
  have hTpos : T.Nonempty := card_pos.mp (by exact_mod_cast ht)
  obtain ⟨z,hcut,hU,hcS,hcA,hi⟩ := good_center hdim S A T U
    (card_pos.mp (by omega)) hA (hTpos.mono hTU) τ hτ hsmall hlarge hsparse
  have hs : (100:ℝ)≤S.card := by exact_mod_cast hS
  have hSn : (9/10:ℝ)*S.card≤(projected S z).card := by
    have hp : (S.card:ℝ)≤(projected S z).card+orderedCollisions S z+1 := by
      exact_mod_cast projection_loss S z
    linarith
  obtain ⟨hlo,hhi⟩ := actual_cut_bounds q T.card (cut T z).card
    ((∑ i∈range (n+2),q^i)/(∑ i∈range (n+3),q^i)) hq0 ht.le
    (cut_mean_bounds q hq n) hcut
  rw [←quotientCut_card] at hlo hhi
  have hp : (S.card:ℝ)*T.card/(4*q)≤(projected S z).card*(quotientCut T z).card := by
    have hh := mul_le_mul hSn hlo (by positivity : 0≤(T.card:ℝ)/(3*q)) (by positivity)
    apply le_trans _ hh
    apply (div_le_iff₀ (by positivity : 0<4*q)).mpr
    field_simp
    nlinarith
  refine ⟨z,hSn,hlo,hhi,by simpa only [quotientCut_card] using hU.le,hp,?_,hcS,hcA⟩
  have hm : (incidenceCount (projected S z) (quotientCut T z):ℝ)≤ incidenceCount S (cut T z) := by
    exact_mod_cast quotient_incidence_le S T z
  apply hm.trans (hi.le.trans _)
  have hh := (div_le_iff₀ (by positivity : 0<4*q)).mp hp
  apply (div_le_div_iff₀ (pow_pos hq0 2) hq0).mpr
  have hh' := mul_le_mul_of_nonneg_left hh (show 0≤100*τ*q by positivity)
  dsimp only [q] at hh' ⊢
  nlinarith only [hh']

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Real Incidence CapComposition
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Finite K] [FiniteDimensional K V] in
lemma lift_contraction_numeric (A : Finset (Projectivization K V))
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule)))
    (m Q : ℝ) (hm : 0 ≤ m) (hQ : 0 < Q) (hW : (W.card:ℝ) ≤ m)
    (hcol : (orderedCollisions A z:ℝ) ≤ 100*(A.card:ℝ)^2/Q) :
    ((liftCap A z W).card:ℝ) ≤ m+sqrt (100*m/Q)*A.card := by
  apply (liftCap_contraction A z W).trans
  apply add_le_add hW
  have hh : (W.card:ℝ)*orderedCollisions A z ≤ m*(100*(A.card:ℝ)^2/Q) :=
    mul_le_mul hW hcol (by positivity) hm
  apply (sqrt_le_sqrt hh).trans_eq
  rw [show m*(100*(A.card:ℝ)^2/Q)=(100*m/Q)*(A.card:ℝ)^2 by ring,
    sqrt_mul (by positivity),sqrt_sq (by positivity : (0:ℝ) ≤ A.card)]

attribute [local instance] OAI.SharpLogRamsey.Projection.flat_JoinedProjectionPublic_1
local instance flat_JoinedProjectionPublic_3_r3f0c80_1 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
lemma liftedLibrary_card (U : Finset (Projectivization K V))
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule))))
    (M : ℕ) (hM : ∀ z,(F z).card ≤ M) :
    (liftedLibrary U F).card ≤ Fintype.card (Projectivization K V)*M := by
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ z : Projectivization K V,M :=
      sum_le_sum (fun z hz => card_image_le.trans (hM z))
    _ = _ := by simp

theorem eight_projection_library {n : ℕ} (hdim : Module.finrank K V=n+3)
    (U S : Finset (Projectivization K V)) (hSU : S ⊆ U)
    (UT T : Finset (Projectivization K (Module.Dual K V))) (hTU : T ⊆ UT)
    (τ m : ℝ) (hτ : 0 < τ) (hm : 0 ≤ m)
    (hS : 100 ≤ S.card)
    (hsmall : (S.card:ℝ) ≤ (Nat.card K:ℝ)^(n+1)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ) ≤ T.card)
    (hsparse : (incidenceCount S T:ℝ) ≤ τ*S.card*T.card/Nat.card K)
    (F : ∀ z : Projectivization K V, Finset (Finset (Projectivization K (V ⧸ z.submodule))))
    (M : ℕ) (hM : ∀ z,(F z).card ≤ M)
    (hsize : ∀ z W,W ∈ F z → (W.card:ℝ) ≤ m)
    (hcover : ∀ z,
      (9/10:ℝ)*S.card ≤ (projected S z).card →
      (T.card:ℝ)/(3*Nat.card K) ≤ (quotientCut T z).card →
      ((quotientCut T z).card:ℝ) ≤ 2*T.card/Nat.card K →
      ((quotientCut UT z).card:ℝ) ≤ 100*UT.card/Nat.card K →
      (S.card:ℝ)*T.card/(4*Nat.card K) ≤ (projected S z).card*(quotientCut T z).card →
      (incidenceCount (projected S z) (quotientCut T z):ℝ) ≤
        400*τ*(projected S z).card*(quotientCut T z).card/Nat.card K →
      ∃ W ∈ F z,(99/100:ℝ)*(projected S z).card ≤ (projected S z∩W).card)
    (hhalf : sqrt (100*m/(Nat.card K:ℝ)^(n+1)) ≤ 1/2)
    (hpow : (Nat.card K:ℝ)*(sqrt (100*m/(Nat.card K:ℝ)^(n+1)))^7 ≤ 1) :
    ∃ A ∈ powers (liftedLibrary U F) U 8,A ⊆ U ∧
      (A.card:ℝ) ≤ 3*m ∧ (S.card:ℝ)/2 ≤ (S∩A).card ∧
      (powers (liftedLibrary U F) U 8).card ≤
        (Fintype.card (Projectivization K V)*M)^8 := by
  let q : ℝ := Nat.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have h1 : ∀ D ∈ liftedLibrary U F,(D.card:ℝ) ≤ q*m := by
    intro D hD
    obtain ⟨z,_,hz⟩ := mem_biUnion.mp hD
    obtain ⟨W,hW,rfl⟩ := mem_image.mp hz
    have hh : ((liftCap U z W).card:ℝ) ≤ q*W.card := by
      dsimp [q]
      exact_mod_cast liftCap_initial U z W
    exact hh.trans (mul_le_mul_of_nonneg_left (hsize z W hW) hq.le)
  have hstep : ∀ A,A ⊆ U → A.Nonempty → ∃ D ∈ liftedLibrary U F,D ⊆ U ∧
      ((S\D).card:ℝ) ≤ (3/100:ℝ)*S.card ∧
      ((A∩D).card:ℝ) ≤ m+sqrt (100*m/q^(n+1))*A.card := by
    intro A hAU hA
    obtain ⟨z,hSn,hTlo,hThi,hU,hmul,hsp,hcS,hcA⟩ :=
      quotient_data hdim S A T UT hA hTU τ hτ hS hsmall hlarge hsparse
    obtain ⟨W,hW,hcap⟩ := hcover z hSn hTlo hThi hU hmul hsp
    refine ⟨liftCap U z W,mem_biUnion.mpr ⟨z,mem_univ _,mem_image.mpr ⟨W,hW,rfl⟩⟩,
      liftCap_subset U z W,?_,?_⟩
    · have hc : ((projected S z\W).card:ℝ) ≤ (1/100:ℝ)*(projected S z).card := by
        have he : ((projected S z\W).card:ℝ)+(projected S z∩W).card=(projected S z).card := by
          exact_mod_cast card_sdiff_add_card_inter (projected S z) W
        linarith
      have hcol : (orderedCollisions S z:ℝ)+1 ≤ (2/100:ℝ)*S.card := by
        have hs : (100:ℝ) ≤ S.card := by exact_mod_cast hS
        linarith
      simpa only [show (1/100:ℝ)+2/100=3/100 by norm_num] using
        original_support_loss_real S U hSU z W (1/100) (2/100) (by norm_num) hc hcol
    · rw [inter_liftCap A U hAU]
      exact lift_contraction_numeric A z W m (q^(n+1)) hm (pow_pos hq _) (hsize z W hW) hcA.le
  obtain ⟨A,hA,hAU,hsizeA,hcapA⟩ := eight_intersections U S
    (card_pos.mp (by omega)) hSU (liftedLibrary U F) m q (sqrt (100*m/q^(n+1))) hm hq.le
    (sqrt_nonneg _) hhalf hpow h1 hstep
  refine ⟨A,hA,hAU,hsizeA,hcapA,?_⟩
  exact (powers_card _ _ _).trans (Nat.pow_le_pow_left (liftedLibrary_card U F M hM) 8)

end
end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_ProjectionScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Real
open scoped Topology

lemma source_numeric {i : ℕ} {σ q N T b : ℝ}
    (hσ : 1000000000000 ≤ σ) (hqeq : exp σ=q)
    (hN : 0<N) (hT : 0<T) (hNT : N≤T) (hb : b≤σ/5)
    (hlo : q^(i+5)*exp (-b)≤N*T) (hhi : N*T≤2*q^(i+5)) :
    N≤q^(i+3)/100000 ∧ 1000000*q≤T ∧
      sqrt (100*(300000*q^(i+5)/T)/q^(i+3))≤1/2 ∧
      q*(sqrt (100*(300000*q^(i+5)/T)/q^(i+3)))^7≤1 := by
  have hs : 0≤σ := by linarith
  have hq : 0<q := hqeq ▸ exp_pos σ
  have hexp (k : ℕ) : q^k=exp ((k:ℝ)*σ) := by rw [←hqeq,exp_nat_mul]
  have hTlow : exp (12*σ/5)≤T := by
    have he : exp (24*σ/5)≤q^(i+5)*exp (-b) := by
      rw [hexp,←exp_add]
      apply exp_le_exp.mpr
      push_cast
      nlinarith [mul_nonneg (show 0≤(i:ℝ) by positivity) hs]
    have hh : (exp (12*σ/5))^2≤T^2 := by
      rw [←exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show (2:ℝ)*(12*σ/5)=24*σ/5 by ring]
      have hp := mul_le_mul_of_nonneg_right hNT hT.le
      nlinarith only [he,hlo,hp]
    exact (sq_le_sq₀ (exp_pos _).le hT.le).mp hh
  have hNup : N≤2*exp (((i+5:ℕ):ℝ)*σ/2) := by
    have he : (exp (((i+5:ℕ):ℝ)*σ/2))^2=q^(i+5) := by
      rw [hexp,←exp_nat_mul]
      congr 1
      push_cast
      ring
    have hp := mul_le_mul_of_nonneg_left hNT hN.le
    have hn : 0<exp (((i+5:ℕ):ℝ)*σ/2) := exp_pos _
    nlinarith only [hp,hhi,he,hn]
  have hcN : 200000≤exp (σ/2) := by
    have hh := add_one_le_exp (σ/2)
    linarith
  have hsN : exp (((i+5:ℕ):ℝ)*σ/2)*exp (σ/2)≤q^(i+3) := by
    rw [hexp,←exp_add]
    apply exp_le_exp.mpr
    push_cast
    nlinarith [mul_nonneg (show 0≤(i:ℝ) by positivity) hs]
  have hsmall : N≤q^(i+3)/100000 := by
    have hh := mul_le_mul_of_nonneg_left hcN (exp_pos (((i+5:ℕ):ℝ)*σ/2)).le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<100000)).mpr
    nlinarith only [hh,hsN,hNup]
  have hcT : 1000000≤exp (7*σ/5) := by
    have hh := add_one_le_exp (7*σ/5)
    linarith
  have hlarge : 1000000*q≤T := by
    have hh := mul_le_mul_of_nonneg_left hcT hq.le
    have he : q*exp (7*σ/5)=exp (12*σ/5) := by
      rw [←hqeq,←exp_add]
      congr 1
      ring
    rw [he] at hh
    nlinarith only [hh,hTlow]
  have hcR : 30000000≤exp (σ/15) := by
    have hh := add_one_le_exp (σ/15)
    linarith
  have hTR : 30000000*exp (7*σ/3)≤T := by
    have hh := mul_le_mul_of_nonneg_right hcR (exp_pos (7*σ/3)).le
    rw [←exp_add,show σ/15+7*σ/3=12*σ/5 by ring] at hh
    exact hh.trans hTlow
  have heQ : q^(i+5)=q^(i+3)*q^2 := by rw [←pow_add]
  have hratio : 100*(300000*q^(i+5)/T)/q^(i+3)=30000000*q^2/T := by
    rw [heQ]
    field_simp
    ring
  have hr : 30000000*q^2/T≤exp (-σ/3) := by
    apply (div_le_iff₀ hT).mpr
    have hh := mul_le_mul_of_nonneg_left hTR (exp_pos (-σ/3)).le
    have he : exp (-σ/3)*(30000000*exp (7*σ/3))=30000000*q^2 := by
      rw [hexp]
      calc
        _ = 30000000*(exp (-σ/3)*exp (7*σ/3)) := by ring
        _ = _ := by rw [←exp_add]; congr 2; norm_num; ring
    rwa [he] at hh
  have hroot : sqrt (100*(300000*q^(i+5)/T)/q^(i+3))≤exp (-σ/6) := by
    rw [hratio]
    apply (sqrt_le_iff).mpr
    refine ⟨(exp_pos _).le,hr.trans_eq ?_⟩
    rw [←exp_nat_mul]
    congr 1
    norm_num
    ring
  have hhalf : exp (-σ/6)≤1/2 := by
    have he : 2≤exp (σ/6) := by have hh := add_one_le_exp (σ/6); linarith
    rw [show -σ/6=-(σ/6) by ring,exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) he)
  refine ⟨hsmall,hlarge,hroot.trans hhalf,?_⟩
  calc
    _ ≤ q*(exp (-σ/6))^7 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sqrt_nonneg _) hroot _) hq.le
    _ = exp (-σ/6) := by
      rw [←hqeq,←exp_nat_mul,←exp_add]
      congr 1
      norm_num
      ring
    _ ≤ 1 := hhalf.trans (by norm_num)

end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma geom_card_le {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    ∑ i ∈ range r,q^i ≤ q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ,pow_succ]
    calc
      _ ≤ q^r+q^r := Nat.add_le_add_right ih _
      _ = q^r*2 := (Nat.mul_two _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hq

lemma projective_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log ((Fintype.card (Projectivization K V):ℝ)+1) ≤ ((r:ℝ)+1)*Nat.card K := by
  have hqN : 2 ≤ Nat.card K := Finite.one_lt_card
  have hq : (1:ℝ) ≤ Nat.card K := by exact_mod_cast hqN.trans' (by norm_num : 1 ≤ 2)
  have hq0 : (0:ℝ) < Nat.card K := by linarith
  have hcard : (Fintype.card (Projectivization K V):ℝ) ≤ (Nat.card K:ℝ)^r := by
    have hn : Fintype.card (Projectivization K V) ≤ Nat.card K^r := by
      rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
      exact geom_card_le hqN r
    exact_mod_cast hn
  have hpow : 1 ≤ (Nat.card K:ℝ)^r := one_le_pow₀ hq
  have hs : (Fintype.card (Projectivization K V):ℝ)+1 ≤ 2*(Nat.card K:ℝ)^r := by linarith
  apply (log_le_log (by positivity) hs).trans
  rw [log_mul (by norm_num) (pow_ne_zero _ hq0.ne'),log_pow]
  have hl2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hlq : log (Nat.card K:ℝ) ≤ Nat.card K :=
    (log_le_sub_one_of_pos hq0).trans (by linarith)
  have hh := mul_le_mul_of_nonneg_left hlq (show 0 ≤ (r:ℝ) by positivity)
  linarith

lemma pair_log_card {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype (Projectivization K V)]
    [Fintype (Projectivization K (Module.Dual K V))]
    (r : ℕ) (hdim : Module.finrank K V=r) :
    log (((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2+1) ≤
      (2*(r:ℝ)+2)*Nat.card K := by
  have hA := projective_log_card r hdim
  have hB := projective_log_card (K:=K) (V:=Module.Dual K V) r
    (Subspace.dual_finrank_eq.trans hdim)
  let A : ℝ := Fintype.card (Projectivization K V)
  let B : ℝ := Fintype.card (Projectivization K (Module.Dual K V))
  have ha : 0 ≤ A := by positivity
  have hb : 0 ≤ B := by positivity
  have hl2 : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hh : (A+B)*log 2+1 ≤ (A+1)*(B+1) := by nlinarith [mul_nonneg ha hb]
  have hl := log_le_log (by positivity : 0 < (A+B)*log 2+1) hh
  rw [log_mul (by positivity) (by positivity)] at hl
  change log ((A+B)*log 2+1) ≤ _
  change log (A+1) ≤ _ at hA
  change log (B+1) ≤ _ at hB
  linarith

lemma row_cost {q P d B H C J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 1 ≤ P) (hd : 0 ≤ d) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hJ : 0 ≤ J) (hBP : B ≤ C*P)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (100*C+2*J+10)*q*P*(d+P) := by
  have hu2 : log (2:ℝ) ≤ 1 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  have hu3 : log (3:ℝ) ≤ 2 := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hh' : (h:ℝ) ≤ 21*q*(d+2) := by nlinarith
  have hmul := mul_le_mul hh' hBP hB (show 0 ≤ 21*q*(d+2) by positivity)
  have hdP : d+2 ≤ 2*(d+P) := by linarith
  have hmul' := mul_le_mul_of_nonneg_left hdP (show 0 ≤ 21*C*q*P by positivity)
  let v := q*P*(d+P)
  have hvq : q ≤ v := by
    have hp : 1 ≤ P*(d+P) := one_le_mul_of_one_le_of_one_le hP (by linarith)
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ q by linarith)
    dsimp only [v]; nlinarith only [hh]
  have hv : 1 ≤ v := hq.trans hvq
  have hj := mul_le_mul_of_nonneg_left hvq hJ
  have hp : 0 ≤ C*v := by positivity
  dsimp only [v] at *
  nlinarith

lemma scheduleLength_le {q u t : ℝ} (hq : 0 ≤ q) (ht : 0 < t) (htu : t ≤ u) :
    (scheduleLength q u t:ℝ) ≤ 20*q*(log (u/t)+2)+1 := by
  have hl : 0 ≤ log (u/t) := log_nonneg ((le_div_iff₀ ht).mpr (by simpa using htu))
  exact (Nat.ceil_lt_add_one (by positivity)).le

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationExtend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma incidenceCount_mono_left {S S' : Finset (Projectivization K V)}
    (h : S'⊆S) (T : Finset (Projectivization K (Module.Dual K V))) :
    incidenceCount S' T≤ incidenceCount S T := by
  unfold incidenceCount
  exact sum_le_sum (fun _ _ => card_le_card (filter_subset_filter _ h))

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
variable [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

theorem extend_cover_fraction {n : ℕ} (hdim : Module.finrank K V=n+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (htu : t≤U.card) (c b : ℝ) (hc : 1 ≤ c) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(n+3)) :
    let q : ℝ := Nat.card K
    let h := scheduleLength q U.card t
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let E := 2*((h:ℝ)*(b+log c)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
      (∀ E∈caps,E⊆U ∧ (E.card:ℝ)≤(1000*c)*q^(n+3)/N) ∧
      (∀ S T,S.card=N → T⊆U → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(N:ℝ)/c≤(S∩W).card) →
        ∃ E∈caps,(99/100:ℝ)*t≤(T∩E).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let q : ℝ := Nat.card K
  let h := scheduleLength q U.card t
  let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
  let E := 2*((h:ℝ)*(b+log c)+log 2+log (H+1))+log 3
  have hlog2 : 0≤log (2:ℝ) := log_nonneg (by norm_num)
  have hlogc : 0≤log c := log_nonneg hc
  have hcp : 0 < c := by linarith
  have hE : 0≤E := by
    have hH : 0≤H := mul_nonneg (by positivity) hlog2
    have hlogH : 0≤log (H+1) := log_nonneg (by linarith)
    have hlog3 : 0≤log (3:ℝ) := log_nonneg (by norm_num)
    dsimp only [E]
    positivity
  have hall (W : Finset (Projectivization K V)) :
      ∃ caps : Finset (Finset (Projectivization K (Module.Dual K V))),
        (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤(1000*c)*q^(n+3)/N) ∧
        (∀ z,CoverInput W U N t c (b+log c) z →
          ∃ F∈caps,(99/100:ℝ)*t≤(z.2∩F).card) ∧
        log ((caps.card:ℝ)+1)≤E := by
    by_cases hW : W.Nonempty
    · obtain ⟨caps,hs,hc,hl⟩ := public_validation_cover hdim W hW U N t hN ht htu
        c (b+log c) hc (add_nonneg hb hlogc) hprod
      refine ⟨caps,?_,hc,hl⟩
      intro F hF
      exact hs F hF
    · have hw : W=∅ := not_nonempty_iff_eq_empty.mp hW
      refine ⟨∅,by simp,?_,?_⟩
      · intro z hz
        exact (hz.1.ne_empty (subset_empty.mp (hw ▸ hz.2.1))).elim
      · simpa using hE
  choose family hfsize hfcapture hflen using hall
  let caps := descriptions.biUnion family
  refine ⟨caps,?_,?_,?_⟩
  · intro F hF
    obtain ⟨W,_,hWF⟩ := mem_biUnion.mp hF
    exact hfsize W F hWF
  · intro S T hSN hTU hTt hsp hcap
    obtain ⟨W,hW,hcapture⟩ := hcap
    let X := S∩W
    have hnr : (0:ℝ)<N := by exact_mod_cast hN
    have hxr : (0:ℝ)<X.card := (div_pos hnr hcp).trans_le hcapture
    have hX : X.Nonempty := card_pos.mp (by exact_mod_cast hxr)
    have hNX : (N:ℝ) ≤ c*X.card := by
      have hh := (div_le_iff₀ hcp).mp hcapture
      linarith
    have hratio : (W.card:ℝ)≤exp (b+log c)*X.card := by
      apply (hsize W hW).trans
      rw [exp_add,exp_log hcp]
      nlinarith only [mul_le_mul_of_nonneg_right hNX (exp_pos b).le]
    have hq : 0<q := by
      dsimp only [q]
      exact_mod_cast Nat.card_pos (α:=K)
    have hspX : (incidenceCount X T:ℝ)≤(X.card:ℝ)*T.card/(10000*Nat.card K) := by
      have hmono : (incidenceCount X T:ℝ)≤ incidenceCount S T := by
        exact_mod_cast incidenceCount_mono_left inter_subset_left T
      apply hmono.trans (hsp.trans _)
      rw [hTt]
      have ht0 : (0:ℝ)≤t := by positivity
      have hh := mul_le_mul_of_nonneg_right hNX ht0
      dsimp only [q] at hq ⊢
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hhq := mul_le_mul_of_nonneg_right hh hq.le
      nlinarith only [hhq]
    have hi : CoverInput W U N t c (b+log c) (X,T) :=
      ⟨hX,inter_subset_right,hNX,hratio,hTU,hTt,hspX⟩
    obtain ⟨F,hF,hcapF⟩ := hfcapture W (X,T) hi
    exact ⟨F,mem_biUnion.mpr ⟨W,hW,hF⟩,hcapF⟩
  · have he := one_le_exp_iff.mpr hE
    have hf (W : Finset (Projectivization K V)) : ((family W).card:ℝ)≤exp E := by
      have hh := exp_le_exp.mpr (hflen W)
      rw [exp_log (by positivity)] at hh
      linarith
    have hc : (caps.card:ℝ)≤(descriptions.card:ℝ)*exp E := by
      calc
        _ ≤ ∑ W∈descriptions,((family W).card:ℝ) := by exact_mod_cast card_biUnion_le (s:=descriptions) (t:=family)
        _ ≤ ∑ _W∈descriptions,exp E := sum_le_sum (fun W _ => hf W)
        _ = _ := by simp
    have hbound : (caps.card:ℝ)+1≤((descriptions.card:ℝ)+1)*exp E := by nlinarith
    have hl := log_le_log (by positivity : (0:ℝ) < caps.card+1) hbound
    rwa [log_mul (by positivity) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_2
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReturn_5
theorem reverse_extend {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (b : ℝ) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log 2)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(20000*q) →
        (∃ W∈descriptions,(t:ℝ)/2≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) 2 b (by norm_num) hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    simpa only [show (1000:ℝ)*2=2000 by norm_num] using (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*2*Nat.card K) := by
      rw [hinc]
      convert hsp using 1 <;> first | rfl | ring
    obtain ⟨F,hF,hcapture⟩ := hAc T (S.image e) hTt (image_subset_image hSU) hcS hsp' hcap
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [(pullback_cover e U S F (hAs F hF).1).2.2]
    exact hcapture
  · have hc : ((A.image (fun W => W.image e.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image e.symm)
    have hl : log (((A.image (fun W => W.image e.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith)
    exact hl.trans (by simpa only [hcU] using hAl)

lemma reverse_size (q N t C b : ℝ) (r : ℕ) (_hq : 0<q) (hN : 0<N) (hC : 0<C)
    (hprod : q^r*exp (-b)≤N*t) : C*q^r/N≤t*exp (b+log C) := by
  rw [exp_add,exp_log hC]
  apply (div_le_iff₀ hN).mpr
  have h := mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  rw [mul_assoc,←exp_add,neg_add_cancel,exp_zero,mul_one] at h
  nlinarith only [mul_le_mul_of_nonneg_left h hC.le]

theorem return_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (c B b : ℝ) (hc : 2 ≤ c) (hB : 0≤B) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp B)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K V):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K V)))*log 2
    let H' := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E₁ := 2*((scheduleLength q UT.card t:ℝ)*(B+log c)+log 2+log (H+1))+log 3
    let E₂ := 2*((scheduleLength q U.card N:ℝ)*(b+log (1000*c)+log 2)+log 2+log (H'+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤2000*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(N:ℝ)/c≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E₁+E₂ := by
  dsimp only
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hdim descriptions UT N t hN ht htU c B
    (by linarith) hB hsize hprod
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc0 : 0 < c := by linarith
  have hsA (W) (hW : W∈A) : (W.card:ℝ)≤t*exp (b+log (1000*c)) :=
    (hAs W hW).2.trans (reverse_size (Nat.card K) N t (1000*c) b (r+3) hq hn (by positivity) hprodlo)
  obtain ⟨F,hFs,hFc,hFl⟩ := reverse_extend hdim A U N t hN ht hNU (b+log (1000*c))
    (add_nonneg hb (log_nonneg (by linarith))) hsA hprod
  refine ⟨F,hFs,?_,hFl.trans (by linarith only [hAl])⟩
  intro S T hSU hSN hTU hTt hsp hcap
  obtain ⟨W,hW,hcapture⟩ := hAc S T hSN hTU hTt hsp hcap
  apply hFc S T hSU hSN hTt _ ⟨W,hW,by linarith⟩
  apply hsp.trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

local instance flat_JoinedValidationReverse_2_r3f0c80_1 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReverse_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationReverse_5
theorem reverse_extend_fraction {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V)) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (c b : ℝ) (hc : 1 ≤ c) (hb : 0≤b)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp b)
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    let q : ℝ := Nat.card K
    let H := ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+
      Fintype.card (Projectivization K (Module.Dual K (Module.Dual K V))))*log 2
    let E := 2*((scheduleLength q U.card N:ℝ)*(b+log c)+log 2+log (H+1))+log 3
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤(1000*c)*q^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(10000*c*q) →
        (∃ W∈descriptions,(t:ℝ)/c≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1)≤log ((descriptions.card:ℝ)+1)+E := by
  dsimp only
  let e := bidual (K:=K) (V:=V)
  have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
  have hd : Module.finrank K (Module.Dual K V)=r+3 := Subspace.dual_finrank_eq.trans hdim
  obtain ⟨A,hAs,hAc,hAl⟩ := extend_cover_fraction hd descriptions (U.image e) t N ht hN
    (by rwa [hcU]) c b hc hb hsize (by simpa [mul_comm] using hprod)
  refine ⟨A.image (fun W => W.image e.symm),?_,?_,?_⟩
  · intro W hW
    obtain ⟨F,hF,rfl⟩ := mem_image.mp hW
    obtain ⟨hFU,hcard,_⟩ := pullback_cover e U ∅ F (hAs F hF).1
    refine ⟨hFU,?_⟩
    rw [hcard]
    exact (hAs F hF).2
  · intro S T hSU hSN hTt hsp hcap
    have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
    have hcS : (S.image e).card=N := (card_image_of_injective _ e.injective).trans hSN
    have hsp' : (incidenceCount T (S.image e):ℝ)≤(t:ℝ)*N/(10000*c*Nat.card K) := by
      rw [hinc]
      convert hsp using 1 <;> first | rfl | ring
    obtain ⟨F,hF,hcapture⟩ := hAc T (S.image e) hTt (image_subset_image hSU) hcS hsp' hcap
    refine ⟨F.image e.symm,mem_image.mpr ⟨F,hF,rfl⟩,?_⟩
    rw [(pullback_cover e U S F (hAs F hF).1).2.2]
    exact hcapture
  · have hc : ((A.image (fun W => W.image e.symm)).card:ℝ)≤A.card := by
      exact_mod_cast card_image_le (s:=A) (f:=fun W => W.image e.symm)
    have hl : log (((A.image (fun W => W.image e.symm)).card:ℝ)+1)≤log ((A.card:ℝ)+1) :=
      log_le_log (by positivity) (by linarith)
    exact hl.trans (by simpa only [hcU] using hAl)

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Validation_ValidationGapCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Validation
open Finset Real Incidence
open scoped Classical BigOperators
noncomputable section

lemma row_cost_sum {q P d e B H J : ℝ} {h : ℕ}
    (hq : 1 ≤ q) (hP : 200000 ≤ P) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hB : 0 ≤ B) (hBP : B ≤ 7*P) (hJ : 0 ≤ J)
    (hh : (h:ℝ) ≤ 20*q*(d+2)+1) (hH : log (H+1) ≤ J*q) :
    2*((h:ℝ)*B+log 2+log (H+1))+log 3 ≤
      (710+2*J)*q*P*(d+e+P) := by
  have hr := row_cost hq (by linarith : 1 ≤ P) hd hB (by norm_num : (0:ℝ) ≤ 7)
    hJ hBP hh hH
  rw [show (100:ℝ)*7+2*J+10=710+2*J by ring] at hr
  apply hr.trans
  gcongr
  linarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma log_hundred : log (100:ℝ) ≤ 99 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100)
  norm_num at hh ⊢
  exact hh
lemma log_hundred_thousand : log (100000:ℝ) ≤ 99999 := by
  have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<100000)
  norm_num at hh ⊢
  exact hh

attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_1
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_3
attribute [local instance] OAI.SharpLogRamsey.Validation.flat_JoinedValidationGapCosts_5
theorem return_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K V)))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P b : ℝ) (hP : 200000≤P) (hb : 0≤b) (hbP : b≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤N*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3))
    (hprodlo : (Nat.card K:ℝ)^(r+3)*exp (-b)≤(N:ℝ)*t) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T⊆UT → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(N:ℝ)/100≤(S∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := return_cover hdim descriptions U UT N t hN ht hNU htU
    100 (6*P) b (by norm_num) (by positivity) hb hsize hprod hprodlo
  refine ⟨A,?_,?_,?_⟩
  · intro F hF
    refine ⟨(hs F hF).1,(hs F hF).2.trans ?_⟩
    gcongr
    norm_num
  · intro S T hSU hSN hTU hTt hsp hcap
    exact hc S T hSU hSN hTU hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB1 : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hB2 : b+log ((1000:ℝ)*100)+log 2≤7*P := by
      have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      norm_num only [show (1000:ℝ)*100=100000 by norm_num]
      linarith only [hbP,hP,log_hundred_thousand,hh]
    have hH1 := pair_log_card (r+3) hdim
    have hH2 := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E1 := row_cost_sum hq hP he hd
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB1
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) ht' htu) hH1
    have E2 := row_cost_sum hq hP hd he
      (add_nonneg (add_nonneg hb (log_nonneg (by norm_num))) (log_nonneg (by norm_num))) hB2
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH2
    have hz : 0≤q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E1 E2
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    have hcombined := add_le_add E1 E2
    ring_nf at hcombined hl hz ⊢
    linarith only [hl,hcombined,hz]

theorem reverse_gap_cover {r : ℕ} (hdim : Module.finrank K V=r+3)
    (descriptions : Finset (Finset (Projectivization K (Module.Dual K V))))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (N t : ℕ)
    (hN : 0<N) (ht : 0<t) (hNU : N≤U.card) (htU : t≤UT.card)
    (P : ℝ) (hP : 200000≤P)
    (hsize : ∀ W∈descriptions,(W.card:ℝ)≤t*exp (6*P))
    (hprod : (N:ℝ)*t≤2*(Nat.card K:ℝ)^(r+3)) :
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ F∈caps,F⊆U ∧ (F.card:ℝ)≤100000*(Nat.card K:ℝ)^(r+3)/t) ∧
      (∀ S T,S⊆U → S.card=N → T.card=t →
        (incidenceCount S T:ℝ)≤(N:ℝ)*t/(1000000*Nat.card K) →
        (∃ W∈descriptions,(t:ℝ)/100≤(T∩W).card) →
        ∃ F∈caps,(99/100:ℝ)*N≤(S∩F).card) ∧
      log ((caps.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+
        (1500+8*(r:ℝ))*(Nat.card K:ℝ)*P*
          (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/t)+P) := by
  obtain ⟨A,hs,hc,hl⟩ := reverse_extend_fraction hdim descriptions U N t hN ht hNU
    100 (6*P) (by norm_num) (by positivity) hsize hprod
  refine ⟨A,?_,?_,?_⟩
  · simpa only [show (1000:ℝ)*100=100000 by norm_num] using hs
  · intro S T hSU hSN hTt hsp hcap
    exact hc S T hSU hSN hTt (by simpa only [show (10000:ℝ)*100=1000000 by norm_num] using hsp) hcap
  · let q : ℝ := Nat.card K
    let d := log ((U.card:ℝ)/N)
    let e := log ((UT.card:ℝ)/t)
    have hq : 1≤q := by
      change (1:ℝ)≤(Nat.card K:ℝ)
      exact_mod_cast Nat.card_pos (α:=K)
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have ht' : (0:ℝ)<t := by exact_mod_cast ht
    have hnu : (N:ℝ)≤U.card := by exact_mod_cast hNU
    have htu : (t:ℝ)≤UT.card := by exact_mod_cast htU
    have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr (by simpa using hnu))
    have he : 0≤e := log_nonneg ((le_div_iff₀ ht').mpr (by simpa using htu))
    have hB : 6*P+log 100≤7*P := by linarith only [log_hundred,hP]
    have hH := pair_log_card (K:=K) (V:=Module.Dual K V) (r+3)
      (Subspace.dual_finrank_eq.trans hdim)
    have E := row_cost_sum hq hP hd he
      (add_nonneg (by positivity) (log_nonneg (by norm_num))) hB
      (show 0≤2*((r+3:ℕ):ℝ)+2 by positivity)
      (scheduleLength_le (by linarith : 0≤q) hn hnu) hH
    have hz : 0≤q*P*(d+e+P) := by positivity
    have hr : 0≤(r:ℝ)*q*P*(d+e+P) := by positivity
    simp only [Nat.cast_add,Nat.cast_ofNat] at E
    change log ((A.card:ℝ)+1) ≤ log ((descriptions.card:ℝ)+1)+(1500+8*(r:ℝ))*q*P*(d+e+P)
    dsimp only [q,d,e] at *
    nlinarith only [hl,E,hz,hr]

end
end SharpLogRamsey.Validation

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientHeaderGaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Projection
open Real

lemma quotient_gap_bounds {q U UT Z W N A T B : ℝ}
    (hq : 0<q) (hN : 0<N) (hT : 0<T) (hA : 0<A) (hB : 0<B)
    (hNA : (9/10:ℝ)*N≤A) (hTB : T/(3*q)≤B)
    (hAU : A≤Z) (hBW : B≤W) (hZU : Z≤U) (hW : W≤100*UT/q) :
    log (Z/A) ≤ log (U/N)+1 ∧ log (W/B) ≤ log (UT/T)+299 := by
  have hU : 0<U := lt_of_lt_of_le hA (hAU.trans hZU)
  have hUT : 0<UT := by
    have hh : 0<100*UT/q := lt_of_lt_of_le hB (hBW.trans hW)
    have hh' := (div_pos_iff.mp hh)
    rcases hh' with hh'|hh'
    · linarith [hh'.1]
    · linarith [hh'.2]
  have hZU' : 0<Z := lt_of_lt_of_le hA hAU
  have hW' : 0<W := lt_of_lt_of_le hB hBW
  have h1 : Z/A≤2*(U/N) := by
    apply (div_le_iff₀ hA).mpr
    have ha : N≤2*A := by linarith
    have hh := mul_le_mul_of_nonneg_left ha (le_of_lt (div_pos hU hN))
    rw [div_mul_cancel₀ _ (ne_of_gt hN)] at hh
    nlinarith only [hh,hZU]
  have h2 : W/B≤300*(UT/T) := by
    apply (div_le_iff₀ hB).mpr
    have hb := (div_le_iff₀ (by positivity : 0<3*q)).mp hTB
    have hh := mul_le_mul_of_nonneg_left hb (show 0≤100*UT/(q*T) by positivity)
    have he1 : 100*UT/(q*T)*T=100*UT/q := by field_simp
    have he2 : 100*UT/(q*T)*(B*(3*q))=300*(UT/T)*B := by field_simp; ring
    rw [he1,he2] at hh
    exact hW.trans hh
  constructor
  · have hh := log_le_log (div_pos hZU' hA) h1
    rw [log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt (div_pos hU hN))] at hh
    have hc := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  · have hh := log_le_log (div_pos hW' hB) h2
    rw [log_mul (by norm_num : (300:ℝ)≠0) (ne_of_gt (div_pos hUT hT))] at hh
    have hc := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<300)
    linarith

end SharpLogRamsey.Projection

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_FiniteHeaderUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicFamilies
open Finset Real
open scoped Classical BigOperators
noncomputable section

lemma union_log_bound {ι α : Type*} [DecidableEq α] (I : Finset ι) (F : ι → Finset α)
    (L : ℝ) (hL : 0≤L) (hF : ∀ i∈I,log ((F i).card+1:ℝ)≤L) :
    log (((I.biUnion F).card:ℝ)+1)≤log ((I.card:ℝ)+1)+L := by
  have hE : 1≤exp L := one_le_exp_iff.mpr hL
  have hF' : ∀ i∈I,((F i).card:ℝ)≤exp L := by
    intro i hi
    have hh := exp_le_exp.mpr (hF i hi)
    rw [exp_log (by positivity)] at hh
    linarith
  have hc : ((I.biUnion F).card:ℝ)≤∑ i∈I,((F i).card:ℝ) := by
    exact_mod_cast card_biUnion_le
  have hs := sum_le_sum hF'
  simp only [sum_const,nsmul_eq_mul] at hs
  have hh : ((I.biUnion F).card:ℝ)+1≤((I.card:ℝ)+1)*exp L := by nlinarith
  have hl := log_le_log (by positivity : 0<((I.biUnion F).card:ℝ)+1) hh
  rw [log_mul (by positivity) (ne_of_gt (exp_pos _)),log_exp] at hl
  exact hl

lemma card_le_ceil_exp {α : Type*} (F : Finset α) (L : ℝ)
    (hF : log ((F.card:ℝ)+1)≤L) : F.card≤⌈exp L⌉₊ := by
  have hh := exp_le_exp.mpr hF
  rw [exp_log (by positivity)] at hh
  have hc : (F.card:ℝ)≤exp L := by linarith
  exact_mod_cast hc.trans (Nat.le_ceil (exp L))

lemma log_ceil_exp {L : ℝ} (hL : 0≤L) :
    log ((⌈exp L⌉₊:ℝ)+1)≤L+2 := by
  have hh : (⌈exp L⌉₊:ℝ)<exp L+1 := Nat.ceil_lt_add_one (exp_pos _).le
  have hE : 1≤exp L := one_le_exp_iff.mpr hL
  have hl := log_le_log (by positivity : (0:ℝ)<(⌈exp L⌉₊:ℝ)+1)
    (show (⌈exp L⌉₊:ℝ)+1≤3*exp L by linarith)
  rw [log_mul (by norm_num : (3:ℝ)≠0) (ne_of_gt (exp_pos _)),log_exp] at hl
  have h3 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
  linarith

end
end SharpLogRamsey.PublicFamilies

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_SizeHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PublicFamilies
open Finset Real
open scoped Classical
noncomputable section

theorem size_header_library {α β : Type*} (A B : ℕ) (Good : ℕ → ℕ → Prop)
    (Size : Finset α → Prop) (Eligible : Finset α → Finset β → Prop)
    (Capture : Finset α → Finset α → Prop) (L : ℝ) (hL : 0≤L)
    (h : ∀ a≤A,∀ b≤B,Good a b → ∃ F : Finset (Finset α),
      (∀ W∈F,Size W) ∧
      (∀ S T,S.card=a → T.card=b → Eligible S T → ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤L) :
    ∃ F : Finset (Finset α),(∀ W∈F,Size W) ∧
      (∀ S T,S.card≤A → T.card≤B → Good S.card T.card → Eligible S T →
        ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤log ((((A+1)*(B+1):ℕ):ℝ)+1)+L := by
  let I := Fin (A+1) × Fin (B+1)
  have hex : ∀ j : I,∃ F : Finset (Finset α),
      (∀ W∈F,Size W) ∧
      (Good j.1 j.2 → ∀ S T,S.card=(j.1:ℕ) → T.card=(j.2:ℕ) → Eligible S T →
        ∃ W∈F,Capture S W) ∧ log ((F.card:ℝ)+1)≤L := by
    intro j
    by_cases hg : Good j.1 j.2
    · obtain ⟨F,hFs,hFc,hFl⟩ := h j.1 (by omega) j.2 (by omega) hg
      exact ⟨F,hFs,fun _ => hFc,hFl⟩
    · refine ⟨∅,by simp,?_,by simpa using hL⟩
      exact fun hh => False.elim (hg hh)
  choose F hF using hex
  refine ⟨univ.biUnion F,?_,?_,?_⟩
  · intro W hW
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hW
    exact (hF j).1 W hj
  · intro S T hSA hTB hg he
    let j : I := (⟨S.card,by omega⟩,⟨T.card,by omega⟩)
    obtain ⟨W,hW,hcap⟩ := (hF j).2.1 hg S T rfl rfl he
    exact ⟨W,mem_biUnion.mpr ⟨j,mem_univ _,hW⟩,hcap⟩
  · have hh := union_log_bound (univ : Finset I) F L hL (fun j _ => (hF j).2.2)
    simp only [card_univ,I,Fintype.card_prod,Fintype.card_fin] at hh
    exact hh

end
end SharpLogRamsey.PublicFamilies

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Learning_EnumeratedCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.DescriptionEnumeration
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {α : Type*}

lemma choose_exp_bound {N n : ℕ} (hn : 0<n) :
    (N.choose n:ℝ) ≤ exp (n*(log ((N:ℝ)/n)+1)) := by
  by_cases hN : N=0
  · subst N
    rw [Nat.choose_eq_zero_of_lt hn]
    simp only [Nat.cast_zero]
    exact (exp_pos _).le
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hN' : (0:ℝ)<N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hfact : (0:ℝ)<n.factorial := by exact_mod_cast Nat.factorial_pos n
  have he := Real.pow_div_factorial_le_exp (n:ℝ) (show (0:ℝ)≤n by positivity) n
  have hf : (1:ℝ)/n.factorial≤exp n/(n:ℝ)^n := by
    apply (div_le_div_iff₀ hfact (pow_pos hn' n)).mpr
    have hh := (div_le_iff₀ hfact).mp he
    simpa only [one_mul] using hh
  calc
    (N.choose n:ℝ) ≤ (N:ℝ)^n/n.factorial := Nat.choose_le_pow_div n N
    _ ≤ (N:ℝ)^n*(exp n/(n:ℝ)^n) := by
      simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hf (pow_nonneg hN'.le n)
    _ = exp n*((N:ℝ)/n)^n := by rw [div_pow]; ring
    _ = exp (n*(log ((N:ℝ)/n)+1)) := by
      rw [mul_add,mul_one,exp_add,exp_nat_mul,exp_log (div_pos hN' hn')]
      ring

theorem public_cover (U : Finset α) (n : ℕ) (hn : 0<n) (hnu : n≤U.card) :
    let caps := U.powersetCard n
    (∀ W∈caps,W⊆U ∧ W.card=n) ∧
    (∀ S,S⊆U → S.card=n → ∃ W∈caps,S∩W=S) ∧
    log ((caps.card:ℝ)+1)≤log 2+n*(log ((U.card:ℝ)/n)+1) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro W hW
    exact mem_powersetCard.mp hW
  · intro S hSU hSn
    exact ⟨S,mem_powersetCard.mpr ⟨hSU,hSn⟩,inter_self S⟩
  · rw [card_powersetCard]
    have hn' : (0:ℝ)<n := by exact_mod_cast hn
    have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
    have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
    have hb : 0≤(n:ℝ)*(log ((U.card:ℝ)/n)+1) := by positivity
    have h := choose_exp_bound (N:=U.card) hn
    have he := one_le_exp_iff.mpr hb
    have hm : ((U.card.choose n:ℝ)+1)≤2*exp (n*(log ((U.card:ℝ)/n)+1)) := by linarith
    have hl := log_le_log (by positivity : (0:ℝ)<(U.card.choose n:ℝ)+1) hm
    rwa [log_mul (by norm_num) (exp_ne_zero _),log_exp] at hl

end
end SharpLogRamsey.DescriptionEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

lemma quotient_product {q b : ℝ} (hq : 0<q) (r : ℕ) :
    q^(r+3)*exp (-(b+log 4))=q^(r+4)*exp (-b)/(4*q) := by
  have he : exp (-(b+log 4))=exp (-b)/4 := by
    simp only [neg_add,exp_add,exp_neg,exp_log (by norm_num : (0:ℝ)<4),div_eq_mul_inv]
  rw [he,show r+4=(r+3)+1 by omega,pow_succ q (r+3)]
  field_simp

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionMessageCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Validation
open scoped Classical
noncomputable section

lemma pair_header_log (A B : ℕ) :
    log ((((A+1)*(B+1):ℕ):ℝ)+1)≤log ((A:ℝ)+1)+log ((B:ℝ)+1)+1 := by
  have hm : (1:ℝ)≤((A:ℝ)+1)*((B:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) A,Nat.cast_nonneg (α:=ℝ) B]
  have he : ((((A+1)*(B+1):ℕ):ℝ)+1)≤2*(((A:ℝ)+1)*((B:ℝ)+1)) := by
    push_cast
    linarith
  have hh := log_le_log (by positivity) he
  rw [log_mul (by norm_num : (2:ℝ)≠0) (by positivity),log_mul (by positivity) (by positivity)] at hh
  have hl := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith

lemma power_pair_log {N A B k : ℕ} (hk : k≠0) (hN : N≤(A*B)^k) :
    log ((N:ℝ)+1)≤(k:ℝ)*(log ((A:ℝ)+1)+log ((B:ℝ)+1)) := by
  have ha : (0:ℝ)≤A := by positivity
  have hb : (0:ℝ)≤B := by positivity
  have hp : ((A:ℝ)*B)^k+1≤((A:ℝ)*B+1)^k := by
    simpa only [one_pow] using pow_add_pow_le (mul_nonneg ha hb) (by norm_num : (0:ℝ)≤1) hk
  have hmul : (A:ℝ)*B+1≤((A:ℝ)+1)*((B:ℝ)+1) := by nlinarith
  have hc : (N:ℝ)≤((A:ℝ)*B)^k := by exact_mod_cast hN
  have he : (N:ℝ)+1≤(((A:ℝ)+1)*((B:ℝ)+1))^k :=
    (by linarith only [hc] : (N:ℝ)+1≤((A:ℝ)*B)^k+1).trans
      (hp.trans (pow_le_pow_left₀ (by positivity) hmul k))
  have hl := log_le_log (by positivity) he
  rwa [log_pow,log_mul (by positivity) (by positivity)] at hl

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.GeometricCover.flat_JoinedProjectionMessageCost_1
local instance flat_JoinedProjectionMessageCost_3_r3f0c80_1 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
lemma domain_log_le (r : ℕ) (hdim : Module.finrank K V=r)
    (U : Finset (Projectivization K V)) :
    log ((U.card:ℝ)+1)≤((r:ℝ)+1)*Nat.card K := by
  apply le_trans _ (projective_log_card r hdim)
  apply log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right (card_le_univ U) 1

lemma header_log_le (r : ℕ) (hdim : Module.finrank K V=r)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) :
    log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)≤(2*(r:ℝ)+3)*Nat.card K := by
  have h1 := domain_log_le r hdim U
  have h2 := domain_log_le r (Subspace.dual_finrank_eq.trans hdim) UT
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have h := pair_header_log U.card UT.card
  linarith

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_QuotientHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection PublicFamilies
open scoped Classical
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]

theorem quotient_header_library (r : ℕ)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 0<N) (hT : 0<T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 300≤P) (hH : 0≤H)
    (z : Projectivization K V)
    (low : ∀ a c,HeaderOK (Nat.card K) b r N T
      (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (r+3) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,W⊆projected U z ∧ (W.card:ℝ)≤300000*(Nat.card K:ℝ)^(r+4)/T) ∧
      (∀ S T',S⊆projected U z → T'⊆quotientCut UT z →
        HeaderOK (Nat.card K) b r N T
          (projected U z).card (quotientCut UT z).card UT.card S.card T'.card →
        (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/Nat.card K →
        ∃ W∈F,(99/100:ℝ)*S.card≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)+
        2*H*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  let q : ℝ := Nat.card K
  have hq : 0<q := by dsimp only [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  let d := log ((U.card:ℝ)/N)
  let e := log ((UT.card:ℝ)/T)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤e := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let L := 2*H*q*P*(d+e+P)
  have hL : 0≤L := by dsimp only [L]; positivity
  let Good := HeaderOK q b r N T (projected U z).card (quotientCut UT z).card UT.card
  let Size := fun W : Finset (Projectivization K (V ⧸ z.submodule)) =>
    W⊆projected U z ∧ (W.card:ℝ)≤300000*q^(r+4)/T
  let Eligible := fun (S : Finset (Projectivization K (V ⧸ z.submodule)))
    (T' : Finset (Projectivization K (Module.Dual K (V ⧸ z.submodule)))) =>
    S⊆projected U z ∧ T'⊆quotientCut UT z ∧
      (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/q
  let Capture := fun S W : Finset (Projectivization K (V ⧸ z.submodule)) =>
    (99/100:ℝ)*S.card≤(S∩W).card
  have hex : ∀ a≤U.card,∀ c≤UT.card,Good a c → ∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,Size W) ∧
      (∀ S T',S.card=a → T'.card=c → Eligible S T' → ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤L := by
    intro a ha c hc hg
    obtain ⟨F,hFs,hFc,hFl⟩ := low a c hg
    obtain ⟨hapos,hcpos,haZ,hcW,hNa,hTc,_hlo,_hhi,hcut⟩ := hg
    have ha' : (0:ℝ)<a := by exact_mod_cast hapos
    have hc' : (0:ℝ) < c := by exact_mod_cast hcpos
    refine ⟨F,?_,?_,?_⟩
    · intro W hW
      refine ⟨(hFs W hW).1,(hFs W hW).2.trans ?_⟩
      apply (div_le_div_iff₀ hc' ht).mpr
      have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity : 0<3*q)).mp hTc)
        (show 0≤100000*q^(r+3) by positivity)
      dsimp only [q] at hh ⊢
      rw [show r+4=(r+3)+1 by omega,pow_succ]
      convert hh using 1 <;> ring
    · intro S T' hSa hT'c hh
      obtain ⟨hS,hT',hsp⟩ := hh
      have hsp' : (incidenceCount S T':ℝ)≤(400*τ)*(a:ℝ)*c/Nat.card K := by
        simpa only [hSa,hT'c] using hsp
      obtain ⟨W,hW,hcap⟩ := hFc S T' hS hSa hT' hT'c hsp'
      exact ⟨W,hW,by simpa only [Capture,hSa] using hcap⟩
    · have hgaps := quotient_gap_bounds hq hn ht ha' hc' hNa hTc
        (show (a:ℝ)≤(projected U z).card by exact_mod_cast haZ)
        (show (c:ℝ)≤(quotientCut UT z).card by exact_mod_cast hcW)
        (show ((projected U z).card:ℝ)≤U.card by exact_mod_cast projected_card_le U z) hcut
      have hh : log (((projected U z).card:ℝ)/a)+
          log (((quotientCut UT z).card:ℝ)/c)+P≤2*(d+e+P) := by
        dsimp only [d,e] at *
        linarith only [hgaps.1,hgaps.2,hP,hd,he]
      have hm := mul_le_mul_of_nonneg_left hh (show 0≤H*q*P by positivity)
      apply hFl.trans
      convert hm using 1; dsimp only [L,d,e,q]; ring
  obtain ⟨F,hFs,hFc,hFl⟩ := size_header_library U.card UT.card Good Size Eligible Capture L hL hex
  refine ⟨F,hFs,?_,hFl⟩
  intro S T' hS hT' hg hsp
  apply hFc S T'
  · exact (card_le_card hS).trans (projected_card_le U z)
  · apply (card_le_card hT').trans
    rw [quotientCut_card]
    exact card_filter_le _ _
  · exact hg
  · exact ⟨hS,hT',hsp⟩

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionFullDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection PublicFamilies CapComposition Validation
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.GeometricCover.flat_JoinedProjectionFullDescription_1
local instance flat_JoinedProjectionFullDescription_3_r3f0c80_1 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
theorem projection_description (i : ℕ) (hdim : Module.finrank K V=i+5)
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 100≤N) (hT : 0<T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 300≤P) (hH : 0≤H)
    (hτ : 0<τ) (hτsmall : τ≤1/8000)
    (hsmall : (N:ℝ)≤(Nat.card K:ℝ)^(i+3)/100000)
    (hlarge : 1000000*(Nat.card K:ℝ)≤T)
    (hprod : (Nat.card K:ℝ)^(i+5)*exp (-b)≤(N:ℝ)*T)
    (hhalf : sqrt (100*(300000*(Nat.card K:ℝ)^(i+5)/T)/(Nat.card K:ℝ)^(i+3))≤1/2)
    (hpow : (Nat.card K:ℝ)*(sqrt (100*(300000*(Nat.card K:ℝ)^(i+5)/T)/
      (Nat.card K:ℝ)^(i+3)))^7≤1)
    (low : ∀ (z : Projectivization K V) a c,
      HeaderOK (Nat.card K) b (i+1) N T
        (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (i+4) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K V)),
      (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤900000*(Nat.card K:ℝ)^(i+5)/T) ∧
      (∀ S T',S⊆U → S.card=N → T'⊆UT → T'.card=T →
        (incidenceCount S T':ℝ)≤τ*(N:ℝ)*T/Nat.card K →
        ∃ W∈F,(N:ℝ)/2≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤(16*H+24*(i:ℝ)+200)*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  let q : ℝ := Nat.card K
  have hq : (1:ℝ)≤q := by dsimp only [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  let d := log ((U.card:ℝ)/N)
  let e := log ((UT.card:ℝ)/T)
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤e := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let Z := q*P*(d+e+P)
  have hZq : q≤Z := by
    have hh : 1≤P*(d+e+P) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left hh hq0.le
    simpa only [mul_one,mul_assoc,Z] using hm
  have hZ : 0≤Z := hq0.le.trans hZq
  let L := log ((((U.card+1)*(UT.card+1):ℕ):ℝ)+1)+2*H*Z
  have hL : 0≤L := add_nonneg (log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg _))) (by positivity)
  have hf : ∀ z : Projectivization K V,∃ F : Finset (Finset (Projectivization K (V ⧸ z.submodule))),
      (∀ W∈F,W⊆projected U z ∧ (W.card:ℝ)≤300000*q^(i+5)/T) ∧
      (∀ S T',S⊆projected U z → T'⊆quotientCut UT z →
        HeaderOK q b (i+1) N T (projected U z).card (quotientCut UT z).card UT.card S.card T'.card →
        (incidenceCount S T':ℝ)≤400*τ*S.card*T'.card/q →
        ∃ W∈F,(99/100:ℝ)*S.card≤(S∩W).card) ∧ log ((F.card:ℝ)+1)≤L := by
    intro z
    obtain ⟨F,hFs,hFc,hFl⟩ := quotient_header_library (i+1) U UT N T b τ P H (by omega) hT hNU hTU hP hH z
      (by intro a c hg; simpa only [show i+1+3=i+4 by omega] using low z a c hg)
    refine ⟨F,?_,hFc,?_⟩
    · simpa only [show i+1+4=i+5 by omega] using hFs
    · simpa only [L,Z,d,e,q,mul_assoc] using hFl
  choose F hF using hf
  let M : ℕ := ⌈exp L⌉₊
  have hM : ∀ z,(F z).card≤M := fun z => card_le_ceil_exp _ L (hF z).2.2
  let m := 300000*q^(i+5)/T
  let A := powers (liftedLibrary U F) U 8
  let caps := A.filter (fun W => W⊆U ∧ (W.card:ℝ)≤3*m)
  have hAc : A.card≤(Fintype.card (Projectivization K V)*M)^8 :=
    (powers_card _ _ _).trans (Nat.pow_le_pow_left (liftedLibrary_card U F M hM) 8)
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    have hh := (mem_filter.mp hW).2
    refine ⟨hh.1,?_⟩
    convert hh.2 using 1 ; dsimp only [m,q] ; ring
  · intro S T' hSU hSn hT'U hTt hsp
    have hcover : ∀ z,
      (9/10:ℝ)*S.card≤(projected S z).card →
      (T'.card:ℝ)/(3*Nat.card K)≤(quotientCut T' z).card →
      ((quotientCut T' z).card:ℝ)≤2*T'.card/Nat.card K →
      ((quotientCut UT z).card:ℝ)≤100*UT.card/Nat.card K →
      (S.card:ℝ)*T'.card/(4*Nat.card K)≤(projected S z).card*(quotientCut T' z).card →
      (incidenceCount (projected S z) (quotientCut T' z):ℝ)≤
        400*τ*(projected S z).card*(quotientCut T' z).card/Nat.card K →
      ∃ W∈F z,(99/100:ℝ)*(projected S z).card≤(projected S z∩W).card := by
      intro z h90 hlo _hhi hcut hpr hqs
      apply (hF z).2.1 _ _ (projected_mono hSU z) (quotientCut_mono hT'U z)
      · have ha : 0<(projected S z).card := by
          have hh : (0:ℝ)<(projected S z).card := by rw [hSn] at h90; nlinarith
          exact_mod_cast hh
        have hc : 0<(quotientCut T' z).card := by
          have hh : (0:ℝ)<(quotientCut T' z).card :=
            (by rw [hTt]; positivity : (0:ℝ)<(T'.card:ℝ)/(3*Nat.card K)).trans_le hlo
          exact_mod_cast hh
        refine ⟨ha,hc,card_le_card (projected_mono hSU z),card_le_card (quotientCut_mono hT'U z),
          by simpa only [hSn] using h90,by simpa only [hTt] using hlo,?_,?_,hcut⟩
        · have hh := div_le_div_of_nonneg_right hprod (show 0≤4*q by positivity)
          have heq := quotient_product hq0 (i+1) (b:=b)
          rw [show i+1+3=i+4 by omega,show i+1+4=i+5 by omega] at heq
          rw [←heq] at hh
          apply hh.trans
          simpa only [hSn,hTt,show i+1+3=i+4 by omega] using hpr
        · let : Finite (V ⧸ z.submodule) := Module.finite_of_finite K
          let : Fintype (Projectivization K (V ⧸ z.submodule)) := Fintype.ofFinite _
          let : Finite (Module.Dual K (V ⧸ z.submodule)) := Module.finite_of_finite K
          let : Fintype (Projectivization K (Module.Dual K (V ⧸ z.submodule))) := Fintype.ofFinite _
          have hdimq : Module.finrank K (V ⧸ z.submodule)=(i+1)+3 := by
            have hh := quotient_dimension z
            omega
          apply sparse_product_bound_two hdimq
          apply hqs.trans
          have hh := mul_le_mul_of_nonneg_right (show 400*τ≤1/20 by linarith)
            (show 0≤((projected S z).card:ℝ)*(quotientCut T' z).card/q by positivity)
          convert hh using 1 <;> ring
      · exact hqs
    have hdim' : Module.finrank K V=(i+2)+3 := by omega
    obtain ⟨W,hWA,hWU,hWsize,hWcap,_⟩ := eight_projection_library hdim' U S hSU UT T' hT'U τ m hτ
      (by dsimp only [m]; positivity) (by simpa only [hSn] using hN)
      (by simpa only [hSn,show i+2+1=i+3 by omega] using hsmall)
      (by simpa only [hTt] using hlarge) (by simpa only [hSn,hTt] using hsp)
      F M hM (fun z W hW => (hF z).1 W hW |>.2) hcover
      (by simpa only [m,q,show i+2+1=i+3 by omega] using hhalf)
      (by simpa only [m,q,show i+2+1=i+3 by omega] using hpow)
    exact ⟨W,mem_filter.mpr ⟨hWA,hWU,hWsize⟩,by simpa only [hSn] using hWcap⟩
  · have hh := power_pair_log (by decide : (8:ℕ)≠0) (show caps.card≤(Fintype.card (Projectivization K V)*M)^8 from (card_filter_le A (fun W => W⊆U ∧ (W.card:ℝ)≤3*m)).trans hAc)
    have hc := projective_log_card (i+5) hdim
    have hMlog := log_ceil_exp hL
    have hheader := header_log_le (i+5) hdim U UT
    simp only [Nat.cast_ofNat] at hh
    change log ((caps.card:ℝ)+1)≤_ at hh
    have hsum : log ((caps.card:ℝ)+1)≤8*(((i+5:ℕ):ℝ)+1)*q+8*L+16 := by
      dsimp only [M] at hh
      dsimp only [q] at *
      linarith
    have hLbound : L≤(2*(i:ℝ)+13)*q+2*H*Z := by
      dsimp only [L]
      dsimp only [q] at *
      push_cast at hheader ⊢
      linarith
    have hqZ := mul_le_mul_of_nonneg_left hZq (show 0≤24*(i:ℝ)+152 by positivity)
    have h1Z : 1≤Z := hq.trans hZq
    have hfinal : log ((caps.card:ℝ)+1)≤(16*H+24*(i:ℝ)+200)*Z := by
      push_cast at hsum
      nlinarith only [hsum,hLbound,hqZ,h1Z]
    simpa only [Z,q,d,e,mul_assoc] using hfinal

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_ProjectionDescription
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Incidence Projection
open scoped Classical
noncomputable section

lemma expansion_cap {q P b N T : ℝ} {r : ℕ} (hN : 0<N) (hT : 0<T)
    (hP : 1000000≤P) (hb : b≤P) (hprod : q^r*exp (-b)≤N*T) :
    900000*q^r/T≤N*exp (6*P) := by
  have he := mul_le_mul_of_nonneg_right hprod (exp_pos b).le
  have heq : exp (-b)*exp b=1 := by rw [←exp_add]; simp only [neg_add_cancel,exp_zero]
  have hq : q^r≤N*T*exp b := by
    simpa only [mul_assoc,heq,mul_one] using he
  have hc : (900000:ℝ)≤exp P := by have hh := add_one_le_exp P; linarith
  have hh := mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤900000 by norm_num)
  apply (div_le_iff₀ hT).mpr
  calc
    _ ≤ 900000*(N*T*exp b) := hh
    _ ≤ exp P*(N*T*exp b) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = N*T*exp (P+b) := by rw [exp_add]; ring
    _ ≤ N*T*exp (6*P) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by positivity)
    _ = _ := by ring

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem smaller_side_description (i : ℕ) (hdim : Module.finrank K V=i+5)
    (σ : ℝ) (hσ : 1000000000000≤σ) (hex : exp σ=(Nat.card K:ℝ))
    (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V)))
    (N T : ℕ) (b τ P H : ℝ) (hN : 0<N) (hT : 0<T) (hNT : N≤T)
    (hNU : N≤U.card) (hTU : T≤UT.card) (hP : 1000000≤P) (hH : 0≤H)
    (hbP : b≤P) (hbσ : b≤σ/5) (hτ : 0<τ) (hτsmall : τ≤1/8000)
    (hprod : (Nat.card K:ℝ)^(i+5)*exp (-b)≤(N:ℝ)*T)
    (hprodup : (N:ℝ)*T≤2*(Nat.card K:ℝ)^(i+5))
    (low : ∀ (z : Projectivization K V) a c,
      HeaderOK (Nat.card K) b (i+1) N T
        (projected U z).card (quotientCut UT z).card UT.card a c →
      Validated (Nat.card K) P H (i+4) (projected U z) (quotientCut UT z) a c (400*τ)) :
    ∃ F : Finset (Finset (Projectivization K V)),
      (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤N*exp (6*P)) ∧
      (∀ S T',S⊆U → S.card=N → T'⊆UT → T'.card=T →
        (incidenceCount S T':ℝ)≤τ*(N:ℝ)*T/Nat.card K →
        ∃ W∈F,(N:ℝ)/100≤(S∩W).card) ∧
      log ((F.card:ℝ)+1)≤(16*H+24*(i:ℝ)+1000)*(Nat.card K:ℝ)*P*
        (log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) := by
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  have hd : 0≤log ((U.card:ℝ)/N) := log_nonneg ((le_div_iff₀ hn).mpr
    (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU)))
  have he : 0≤log ((UT.card:ℝ)/T) := log_nonneg ((le_div_iff₀ ht).mpr
    (by simpa only [one_mul] using (show (T:ℝ)≤UT.card by exact_mod_cast hTU)))
  let Z := (Nat.card K:ℝ)*P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P)
  have hZ : 0≤Z := by dsimp only [Z]; positivity
  by_cases hsmall : (N:ℝ)≤200*(Nat.card K:ℝ)*P
  · obtain ⟨hs,hc,hl⟩ := DescriptionEnumeration.public_cover U N hN hNU
    refine ⟨U.powersetCard N,?_,?_,?_⟩
    · intro W hW
      refine ⟨(hs W hW).1,?_⟩
      rw [(hs W hW).2]
      exact le_mul_of_one_le_right hn.le (one_le_exp_iff.mpr (by positivity))
    · intro S T' hSU hSN _hTU _hTt _hsp
      obtain ⟨W,hW,hSW⟩ := hc S hSU hSN
      refine ⟨W,hW,?_⟩
      rw [hSW,hSN]
      linarith
    · have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤log ((U.card:ℝ)/N)+1 by linarith)
      have hh2 := mul_le_mul_of_nonneg_left
        (show log ((U.card:ℝ)/N)+1≤log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P by linarith)
        (show 0≤200*(Nat.card K:ℝ)*P by positivity)
      have hZ1 : 1≤Z := by
        have hbase : 1≤P*(log ((U.card:ℝ)/N)+log ((UT.card:ℝ)/T)+P) :=
          one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
        have hm := one_le_mul_of_one_le_of_one_le hq hbase
        simpa only [Z,mul_assoc] using hm
      have hl2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      have hcoef : (201:ℝ)≤16*H+24*(i:ℝ)+1000 := by have hi := Nat.cast_nonneg (α:=ℝ) i; linarith
      have hzcoef := mul_le_mul_of_nonneg_right hcoef hZ
      have hfinal : log (((U.powersetCard N).card:ℝ)+1)≤(16*H+24*(i:ℝ)+1000)*Z := by
        nlinarith only [hl,hh,hh2,hZ1,hl2,hzcoef]
      simpa only [Z,mul_assoc] using hfinal
  · have hN100 : 100≤N := by
      have hm := mul_le_mul_of_nonneg_right hq (show 0≤200*P by positivity)
      have hn100 : (100:ℝ)≤N := by nlinarith
      exact_mod_cast hn100
    obtain ⟨hs,ht',hh,hpow⟩ := source_numeric hσ hex hn ht
      (by exact_mod_cast hNT) hbσ hprod hprodup
    obtain ⟨F,hFs,hFc,hFl⟩ := projection_description i hdim U UT N T b τ P H hN100 hT hNU hTU
      (by linarith) hH hτ hτsmall hs ht' hprod hh hpow low
    refine ⟨F,?_,?_,?_⟩
    · intro W hW
      exact ⟨(hFs W hW).1,(hFs W hW).2.trans (expansion_cap hn ht hP hbP hprod)⟩
    · intro S T' hSU hSN hTU hTt hsp
      obtain ⟨W,hW,hcap⟩ := hFc S T' hSU hSN hTU hTt hsp
      exact ⟨W,hW,by linarith⟩
    · apply hFl.trans
      have hh := mul_le_mul_of_nonneg_right
        (show 16*H+24*(i:ℝ)+200≤16*H+24*(i:ℝ)+1000 by linarith) hZ
      simpa only [Z,mul_assoc] using hh

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Geometry_GeometricInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

theorem uniform_step (i : ℕ) (H : ℝ) (hH : 0≤H) (ih : Uniform (i+4) H) :
    Uniform (i+5) (16*H+32*(i:ℝ)+3000) := by
  intro η hη C hC
  let C' := 400*C+4
  have hC' : 1≤C' := by dsimp only [C']; linarith
  have hdec : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [ih η hη C' hC',
    eventually_uniform_L hη (eventually_ge_atTop (1000000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    eventually_P_le_linear hη (1/5) (by norm_num),
    hdec.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/1000000)),
    eventually_ge_atTop (1000000000000:ℝ)]
    with σ hs hL hR hbsmall hPσ hτsmall hσ
  intro q _ hq hex V _ _ _ hdim D R had U UT n t b τ hn ht hnu htu hb hbu hτ hτu hplo hphi
  let P := scaleP σ η D R
  have hσ1 : 1≤σ := by linarith
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith [hL D R had]) (hR D R had)
  have hP : 1000000≤P := (hL D R had).trans hLP
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (mul_nonneg (by linarith) (rpow_nonneg (by linarith) _))
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hbσ : b≤σ/5 := hbP.trans (by dsimp only [P]; linarith [hPσ D R had])
  have hsmall : τ≤1/1000000 := hτu.trans hτsmall.le
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hcard : Nat.card (ZMod q)=q := by simp
  have hK : 1 ≤ scaleKstar σ η D := by
    have hbpos := (beta_pos hη).le
    have hD : 1≤D := (one_le_rpow hσ1 hbpos).trans had.D_lower
    exact one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ1 (by positivity))
  have hlog4 : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  have hlog4up : log (4:ℝ)≤3 := by have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have hb' : b+log 4≤C'*scaleKstar σ η D := by dsimp only [C']; nlinarith
  have hτ' : 400*τ≤C'*σ^(-100*beta η) := by
    have hh := mul_le_mul_of_nonneg_left hτu (show (0:ℝ)≤400 by norm_num)
    dsimp only [C']
    nlinarith [rpow_nonneg (by linarith : 0≤σ) (-100*beta η)]
  have hdesc (W : Type) [AddCommGroup W] [Module (ZMod q) W] [FiniteDimensional (ZMod q) W]
      (hdW : Module.finrank (ZMod q) W=i+5)
      (A : Finset (Projectivization (ZMod q) W))
      (B : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) W)))
      (a c : ℕ) (ha : 0<a) (hc : 0 < c) (haA : a≤A.card) (hcB : c≤B.card)
      (hac : a ≤ c) (hlo : (q:ℝ)^(i+5)*exp (-b)≤(a:ℝ)*c)
      (hhi : (a:ℝ)*c≤2*(q:ℝ)^(i+5)) :
      Description q P (16*H+24*(i:ℝ)+1000) A B a c τ := by
    have low (z : Projectivization (ZMod q) W) x y
        (hg : HeaderOK (Nat.card (ZMod q)) b (i+1) a c
          (projected A z).card (quotientCut B z).card B.card x y) :
        Validated (Nat.card (ZMod q)) P H (i+4) (projected A z) (quotientCut B z) x y (400*τ) := by
      obtain ⟨hx,hy,hxA,hyB,_ha,_hc,hlo',hhi',_hcut⟩ := hg
      have hdq : Module.finrank (ZMod q) (W ⧸ z.submodule)=i+4 := by
        have hh := quotient_dimension z
        omega
      rw [hcard]
      change Validated q (scaleP σ η D R) H (i+4) (projected A z) (quotientCut B z) x y (400*τ)
      apply hs q hq hex (W ⧸ z.submodule) hdq D R had
        (projected A z) (quotientCut B z) x y (b+log 4) (400*τ) hx hy hxA hyB
        (add_nonneg hb hlog4) hb' (by positivity) hτ'
      · simpa only [hcard,show i+1+3=i+4 by omega] using hlo'
      · simpa only [hcard,show i+1+3=i+4 by omega] using hhi'
    have hh := smaller_side_description i hdW σ hσ (by simpa only [hcard] using hex)
      A B a c b τ P H ha hc hac haA hcB hP hH hbP hbσ hτ (by linarith)
      (by simpa only [hcard] using hlo) (by simpa only [hcard] using hhi) low
    simpa only [hcard,Description] using hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have he : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hz : 0≤(q:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by positivity
  have hspval (S : Finset (Projectivization (ZMod q) V))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (hsp : (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q) :
      (incidenceCount S T:ℝ)≤(n:ℝ)*t/(1000000*Nat.card (ZMod q)) := by
    rw [hcard]
    apply hsp.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤(n:ℝ)*t/q by positivity)
    convert hh using 1 <;> ring
  have hd5 : Module.finrank (ZMod q) V=(i+2)+3 := by omega
  by_cases hnt : n≤t
  · obtain ⟨A,hAs,hAc,hAl⟩ := hdesc V hdim U UT n t hn ht hnu htu hnt hplo hphi
    obtain ⟨F,hFs,hFc,hFl⟩ := return_gap_cover hd5 A U UT n t hn ht hnu htu P b (by linarith) hb hbP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
      (by simpa only [hcard] using hplo)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      exact hFc S T hSU hSn hTU hTt (hspval S T hsp) (hAc S T hSU hSn hTU hTt hsp)
    · simp only [hcard,Nat.cast_add,Nat.cast_ofNat] at hFl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]
  · have htn : t≤n := le_of_not_ge hnt
    let e := bidual (K:=ZMod q) (V:=V)
    have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
    have hddual : Module.finrank (ZMod q) (Module.Dual (ZMod q) V)=i+5 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨A,hAs,hAc,hAl⟩ := hdesc (Module.Dual (ZMod q) V) hddual UT (U.image e) t n
      ht hn htu (by rwa [hcU]) htn (by simpa only [mul_comm] using hplo) (by simpa only [mul_comm] using hphi)
    obtain ⟨F,hFs,hFc,hFl⟩ := reverse_gap_cover hd5 A U UT n t hn ht hnu htu P (by linarith)
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
      have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
      have hspread : (incidenceCount T (S.image e):ℝ)≤τ*(t:ℝ)*n/q := by
        rw [hinc]
        convert hsp using 1 <;> first | rfl | ring
      exact hFc S T hSU hSn hTt (hspval S T hsp)
        (hAc T (S.image e) hTU hTt (image_subset_image hSU) hcS hspread)
    · simp only [hcard,Nat.cast_add,Nat.cast_ofNat] at hFl
      rw [hcU] at hAl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]

theorem uniform_all (i : ℕ) : ∃ H : ℝ,0≤H ∧ Uniform (i+4) H := by
  induction i with
  | zero => exact ⟨7000,by norm_num,uniform_four⟩
  | succ i ih =>
    obtain ⟨H,hH,ih⟩ := ih
    exact ⟨16*H+32*(i:ℝ)+3000,by positivity,uniform_step i H hH ih⟩

end
end SharpLogRamsey.GeometricCover

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_UniformBook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real GeometricCover SourceScales Filter
open scoped Classical Topology
noncomputable section

theorem uniform_book (i : ℕ) : ∃ H : ℝ,0≤H ∧
    ∀ η : ℝ,0<η → ∀ C : ℝ,1≤C →
    ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=i+4 → ∀ D R,Admissible σ η D R →
    ∀ b τ : ℝ,0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
      Nonempty (Book (K:=ZMod q) (V:=V) q b τ (scaleP σ η D R) H (i+4)) := by
  obtain ⟨H,hH,huniform⟩ := uniform_all i
  refine ⟨H,hH,?_⟩
  intro η hη C hC
  let C' := 4*C+4
  have hC' : 1≤C' := by dsimp only [C']; linarith
  filter_upwards [huniform η hη C' hC',eventually_ge_atTop (1:ℝ)] with σ hs hσ
  intro q _ hq hex V _ _ _ hdim D R had b τ hb hbC hτ hτC
  have hK : 1≤ scaleKstar σ η D := by
    have hD : 1≤D := (one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
    exact one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ (by have hb := beta_pos hη; positivity))
  have hlog : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  have hlog' : log (4:ℝ)≤3 := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    linarith
  have hb' : b+log 4≤C'*scaleKstar σ η D := by dsimp only [C']; nlinarith
  have hτ' : 4*τ≤C'*σ^(-100*beta η) := by
    have hpow := rpow_nonneg (show 0≤σ by linarith) (-100*beta η)
    dsimp only [C']
    nlinarith
  refine ⟨Book.ofValidated q b τ (scaleP σ η D R) H (i+4) ?_⟩
  intro U s t hh
  rcases hh with ⟨hs0,ht0,hsU,htU,hlo,hhi⟩
  exact hs q hq hex V hdim D R had U.1 U.2 s t (b+log 4) (4*τ)
    hs0 ht0 hsU htU (add_nonneg hb hlog) hb' (by positivity) hτ' hlo hhi

end
end SharpLogRamsey.ActualPivot

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Parameters_BookScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

lemma Kstar_ge_one {σ η D : ℝ} {R : ℕ} (hσ : 1≤σ) (hη : 0<η)
    (had : Admissible σ η D R) : 1≤ scaleKstar σ η D := by
  apply one_le_mul_of_one_le_of_one_le
  · exact (one_le_rpow hσ (beta_pos hη).le).trans had.D_lower
  · exact one_le_rpow hσ (by have := beta_pos hη; positivity)

lemma P_ge_Kstar {σ η D : ℝ} {R : ℕ} (hσ : 0<σ)
    (had : Admissible σ η D R) :
    scaleKstar σ η D*σ^(3*beta η)≤ scaleP σ η D R := by
  have hD : 0<D := (rpow_pos_of_pos hσ _).trans_le had.D_lower
  calc
    _ = scaleL σ η D*σ^beta η := by
      unfold scaleKstar scaleL
      rw [mul_assoc,mul_assoc,←rpow_add hσ,←rpow_add hσ]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left had.R_lower (by unfold scaleL; positivity)

theorem eventually_book_scales {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R : ℕ),Admissible σ η D R →
      0≤16*scaleKstar σ η D ∧ 4≤ scaleP σ η D R ∧
      16*scaleKstar σ η D+log 1000000≤ scaleP σ η D R ∧
      0<σ^(-100*beta η) ∧ σ^(-100*beta η)≤1/40000 := by
  have hb:=beta_pos hη
  have ht : Tendsto (fun σ : ℝ=>σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa only [neg_mul] using tendsto_rpow_neg_atTop (show 0<100*beta η by positivity)
  filter_upwards [(tendsto_rpow_atTop (show 0<3*beta η by positivity)).eventually_ge_atTop
      (16+log 1000000),ht.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/40000)),
      eventually_ge_atTop (1:ℝ)] with σ hpow hτ hσ D R had
  have hσ0 : 0<σ:=by linarith
  have hK:=Kstar_ge_one hσ hη had
  have hlo:=P_ge_Kstar hσ0 had
  have hlog : 0≤log (1000000:ℝ):=log_nonneg (by norm_num)
  have hKP : 16*scaleKstar σ η D+log 1000000≤ scaleP σ η D R := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (by linarith : 0≤ scaleKstar σ η D),
      mul_le_mul_of_nonneg_left hK hlog]
  exact ⟨by positivity,by linarith,hKP,rpow_pos_of_pos hσ0 _,hτ⟩
end
end SharpLogRamsey.SourceScales

end

end OAI
end

section
-- module Solutions.OAIQ045_SR.SharpRamsey_Windows_SuppliedBook
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Real Filter SourceScales
open scoped Topology
noncomputable section

theorem supplied_book_oai (i : ℕ) : ∃ H : ℝ, 0 ≤ H ∧
    ∀ η : ℝ, 0 < η → ∀ᶠ σ : ℝ in atTop,
    ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ = (q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V = i+4 → ∀ D R, Admissible σ η D R →
    let b := 16*scaleKstar σ η D
    let τ := σ^(-100*beta η)
    0 ≤ b ∧ 4 ≤ scaleP σ η D R ∧ b+log 1000000 ≤ scaleP σ η D R ∧
    0 ≤ τ ∧ τ ≤ 1/40000 ∧
    Nonempty (Book (K:=ZMod q) (V:=V) (Nat.card (ZMod q)) b τ
      (scaleP σ η D R) H ((i+1)+3)) := by
  obtain ⟨H,hH,hbook⟩ := uniform_book i
  refine ⟨H,hH,?_⟩
  intro η hη
  filter_upwards [hbook η hη 16 (by norm_num), eventually_book_scales hη,
    eventually_ge_atTop (1:ℝ)] with σ hb hs hσ
  intro q _ hq he V _ _ _ hd D R had
  obtain ⟨h0,hP,hbP,hτ,hτsmall⟩ := hs D R had
  dsimp only
  refine ⟨h0,hP,hbP,hτ.le,hτsmall,?_⟩
  simpa only [Nat.card_zmod] using hb q hq he V hd D R had
    (16*scaleKstar σ η D) (σ^(-100*beta η)) h0 le_rfl hτ (by
      have hh := rpow_nonneg (by linarith : 0 ≤ σ) (-100*beta η)
      linarith)
end
end SharpLogRamsey.ActualPivot

end

end OAI
end

theorem solution : type_of% @OAI.SharpLogRamsey.ActualPivot.supplied_book_oai := @OAI.SharpLogRamsey.ActualPivot.supplied_book_oai
