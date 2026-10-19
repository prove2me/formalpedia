-- Prove2me | solution 1 for OAI.CriticalZ3.critical_no_infinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:23:18.383852+00:00
-- url     : https://prove2.me/submissions/fa0d5354-a28d-4f8f-8549-76575dbcd28d

import Mathlib
import Definitions.Def_CriticalZ3

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uE uOmega uV uF uI u uW uD uAlpha

section
section
namespace OAI

open MeasureTheory ProbabilityTheory

namespace CriticalZ3

end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory

namespace CriticalZ3

@[simp] theorem parameter_coe {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    (parameter p : ℝ) = p := by
  simp [parameter, min_eq_right hp.2, max_eq_right hp.1]

@[simp] theorem parameter_zero : parameter 0 = 0 := Subtype.ext (by simp [parameter])
@[simp] theorem parameter_one : parameter 1 = 1 := Subtype.ext (by simp [parameter])

instance bondLaw_probability (p : ℝ) : IsProbabilityMeasure (bondLaw p) := by
  unfold bondLaw
  infer_instance

instance siteLaw_probability (p : ℝ) : IsProbabilityMeasure (siteLaw p) := by
  unfold siteLaw
  infer_instance

@[simp] theorem bondLaw_zero : bondLaw 0 = Measure.dirac (fun _ => false) := by
  simp [bondLaw]

@[simp] theorem siteLaw_zero : siteLaw 0 = Measure.dirac (fun _ => false) := by
  simp [siteLaw]

@[simp] theorem bondLaw_one : bondLaw 1 = Measure.dirac (fun _ => true) := by
  simp [bondLaw]

@[simp] theorem siteLaw_one : siteLaw 1 = Measure.dirac (fun _ => true) := by
  simp [siteLaw]

theorem nearestNeighbor_symm {x y : Vertex} (h : NearestNeighbor x y) :
    NearestNeighbor y x := by
  obtain ⟨i, h⟩ := h
  exact ⟨i, h.symm⟩

theorem bondOpen_symm {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    BondOpen ω y x := h.symm

theorem siteOpen_symm {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    SiteOpen ω y x := ⟨nearestNeighbor_symm h.1, h.2.2, h.2.1⟩

/-- Finite path length, used solely to prove measurability of reachability. -/
def PathLength {V : Type uV} (r : V → V → Prop) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | n + 1, x, y => ∃ z, PathLength r n x z ∧ r z y

theorem pathLength_rtg {V : Type uV} {r : V → V → Prop} {n : ℕ} {x y : V}
    (h : PathLength r n x y) : Relation.ReflTransGen r x y := by
  induction n generalizing y with
  | zero => cases h; exact .refl
  | succ n ih =>
    obtain ⟨z, hz, hy⟩ := h
    exact (ih hz).tail hy

theorem rtg_iff_exists_pathLength {V : Type uV} {r : V → V → Prop} {x y : V} :
    Relation.ReflTransGen r x y ↔ ∃ n, PathLength r n x y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail y z _ hy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, y, hn, hy⟩
  · rintro ⟨n, hn⟩
    exact pathLength_rtg hn

theorem measurableSet_rtg {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → V → Prop) (hr : ∀ x y, MeasurableSet {ω | r ω x y}) (x y : V) :
    MeasurableSet {ω | Relation.ReflTransGen (r ω) x y} := by
  have hpath (n : ℕ) (x y : V) : MeasurableSet {ω | PathLength (r ω) n x y} := by
    induction n generalizing x y with
    | zero => simp only [PathLength]; exact MeasurableSet.const _
    | succ n ih =>
      simp only [PathLength, Set.ofPred_exists]
      exact MeasurableSet.iUnion (fun z => (ih x z).inter (hr z y))
  simp only [rtg_iff_exists_pathLength, Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => hpath n x y)

theorem measurableSet_bondOpen (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondOpen ω x y} := by
  unfold BondOpen
  simp only [Set.ofPred_or, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (x, i)) measurable_const))
  · exact MeasurableSet.iUnion (fun i => (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply (y, i)) measurable_const))

theorem measurableSet_siteOpen (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteOpen ω x y} := by
  exact (MeasurableSet.const _).inter
    ((measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply y) measurable_const))

theorem measurableSet_bondConnected (x y : Vertex) :
    MeasurableSet {ω : BondConfig | BondConnected ω x y} :=
  measurableSet_rtg BondOpen measurableSet_bondOpen x y

theorem measurableSet_siteConnected (x y : Vertex) :
    MeasurableSet {ω : SiteConfig | SiteConnected ω x y} :=
  (measurableSet_eq_fun (measurable_pi_apply x) measurable_const).inter
    (measurableSet_rtg SiteOpen measurableSet_siteOpen x y)

theorem infinite_iff_escape_finset {V : Type uV} (s : Set V) :
    s.Infinite ↔ ∀ t : Finset V, ∃ y ∈ s, y ∉ t := by
  classical
  constructor
  · exact fun hs t => hs.exists_notMem_finset t
  · intro h hs
    obtain ⟨y, hy, hn⟩ := h hs.toFinset
    exact hn (hs.mem_toFinset.mpr hy)

theorem measurableSet_infinite_fiber {Ω : Type uOmega} {V : Type uV} [MeasurableSpace Ω] [Countable V]
    (r : Ω → V → Prop) (hr : ∀ y, MeasurableSet {ω | r ω y}) :
    MeasurableSet {ω | {y | r ω y}.Infinite} := by
  simp only [infinite_iff_escape_finset, Set.mem_ofPred_eq]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  rw [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun y => (hr y).inter (MeasurableSet.const _))

theorem measurableSet_bondInfiniteAt (x : Vertex) : MeasurableSet (bondInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => BondConnected ω x y)
    (measurableSet_bondConnected x)

theorem measurableSet_siteInfiniteAt (x : Vertex) : MeasurableSet (siteInfiniteAt x) :=
  measurableSet_infinite_fiber (fun ω y => SiteConnected ω x y)
    (measurableSet_siteConnected x)

/-- An infinite nearest-neighbor ray, used to certify supercriticality at one. -/
def ray (x : Vertex) (n : ℕ) : Vertex :=
  fun j => x j + if j = 0 then (n : ℤ) else 0

@[simp] theorem ray_zero (x : Vertex) : ray x 0 = x := by
  ext j
  simp [ray]

@[simp] theorem ray_succ (x : Vertex) (n : ℕ) : ray x (n + 1) = step (ray x n) 0 := by
  ext j
  by_cases hj : j = 0
  · subst j; simp [ray, step]; omega
  · simp [ray, step, hj, Ne.symm hj]

theorem ray_injective (x : Vertex) : Function.Injective (ray x) := by
  intro n m h
  have he := congrFun h 0
  simp only [ray] at he
  exact Int.ofNat_inj.mp (add_left_cancel he)

theorem bondConnected_open_ray (x : Vertex) (n : ℕ) :
    BondConnected (fun _ => true) x (ray x n) := by
  induction n with
  | zero => rw [ray_zero]; exact .refl
  | succ n ih =>
    apply ih.tail
    exact Or.inl ⟨0, ray_succ x n, rfl⟩

theorem siteConnected_open_ray (x : Vertex) (n : ℕ) :
    SiteConnected (fun _ => true) x (ray x n) := by
  refine ⟨rfl, ?_⟩
  induction n with
  | zero => rw [ray_zero]
  | succ n ih =>
    apply ih.tail
    exact ⟨⟨0, Or.inl (ray_succ x n)⟩, rfl, rfl⟩

theorem bondCluster_open_infinite (x : Vertex) : (bondCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact bondConnected_open_ray x n)

theorem siteCluster_open_infinite (x : Vertex) : (siteCluster (fun _ => true) x).Infinite :=
  (Set.infinite_range_of_injective (ray_injective x)).mono
    (by rintro y ⟨n, rfl⟩; exact siteConnected_open_ray x n)

@[simp] theorem bondCluster_closed (x : Vertex) : bondCluster (fun _ => false) x = {x} := by
  ext y
  change Relation.ReflTransGen (BondOpen (fun _ => false)) x y ↔ y = x
  apply Relation.reflTransGen_iff_eq
  intro y h
  rcases h with ⟨i, _, hi⟩ | ⟨i, _, hi⟩ <;> cases hi

@[simp] theorem siteCluster_closed (x : Vertex) : siteCluster (fun _ => false) x = ∅ := by
  ext y
  simp [siteCluster, SiteConnected]

@[simp] theorem bondLaw_zero_infinite (x : Vertex) : bondLaw 0 (bondInfiniteAt x) = 0 := by
  rw [bondLaw_zero, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt]

@[simp] theorem siteLaw_zero_infinite (x : Vertex) : siteLaw 0 (siteInfiniteAt x) = 0 := by
  rw [siteLaw_zero, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt]

@[simp] theorem bondLaw_one_infinite (x : Vertex) : bondLaw 1 (bondInfiniteAt x) = 1 := by
  rw [bondLaw_one, Measure.dirac_apply' _ (measurableSet_bondInfiniteAt x)]
  simp [bondInfiniteAt, bondCluster_open_infinite]

@[simp] theorem siteLaw_one_infinite (x : Vertex) : siteLaw 1 (siteInfiniteAt x) = 1 := by
  rw [siteLaw_one, Measure.dirac_apply' _ (measurableSet_siteInfiniteAt x)]
  simp [siteInfiniteAt, siteCluster_open_infinite]

theorem bond_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial⟩

theorem site_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial⟩

theorem bondCritical_mem : bondCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf bond_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial)

theorem siteCritical_mem : siteCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf site_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial)

theorem bond_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < bondCritical) : bondLaw p (bondInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : bondCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

theorem site_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < siteCritical) : siteLaw p (siteInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : siteCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

/-- A path with finitely many types of exceptional arrivals ends in the
unperturbed component of its starting point or of an exceptional vertex. -/
theorem rtg_covered_by_roots {V : Type uV} {r s : V → V → Prop} {F : Set V}
    (h : ∀ a b, r a b → s a b ∨ b ∈ F) {x y : V}
    (hxy : Relation.ReflTransGen r x y) :
    ∃ z ∈ insert x F, Relation.ReflTransGen s z y := by
  induction hxy with
  | refl => exact ⟨x, Set.mem_insert x F, .refl⟩
  | @tail a b _ hab ih =>
    rcases h a b hab with hs | hb
    · obtain ⟨z,hz,hza⟩ := ih
      exact ⟨z,hz,hza.tail hs⟩
    · exact ⟨b,Set.mem_insert_of_mem x hb,.refl⟩

theorem finite_components_of_finite_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hs : ∀ x, {y | Relation.ReflTransGen s x y}.Finite) (x : V) :
    {y | Relation.ReflTransGen r x y}.Finite := by
  apply ((hF.insert x).biUnion (fun z _ => hs z)).subset
  intro y hy
  obtain ⟨z,hz,hzy⟩ := rtg_covered_by_roots h hy
  exact Set.mem_iUnion₂.mpr ⟨z,hz,hzy⟩

theorem infinite_component_of_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hr : ∃ x, {y | Relation.ReflTransGen r x y}.Infinite) :
    ∃ x, {y | Relation.ReflTransGen s x y}.Infinite := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx⟩ := hr
  exact hx (finite_components_of_finite_perturbation hF h hn x)

/-- A negative coordinate step, needed only to list all finitely many neighbors. -/
def backstep (x : Vertex) (i : Fin 3) : Vertex := fun j => x j - if i = j then 1 else 0

@[simp] theorem step_backstep (x : Vertex) (i : Fin 3) : step (backstep x i) i = x := by
  funext j
  simp [step, backstep]

@[simp] theorem backstep_step (x : Vertex) (i : Fin 3) : backstep (step x i) i = x := by
  funext j
  simp [step, backstep]

theorem nearestNeighbor_iff_steps (x y : Vertex) :
    NearestNeighbor x y ↔ ∃ i, y = step x i ∨ y = backstep x i := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,backstep_step])⟩
  · rintro ⟨i,hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,step_backstep])⟩

theorem finite_neighbors (x : Vertex) : {y | NearestNeighbor x y}.Finite := by
  apply ((Set.finite_range (step x)).union (Set.finite_range (backstep x))).subset
  intro y hy
  obtain ⟨i,hi | hi⟩ := (nearestNeighbor_iff_steps x y).mp hy
  · exact Or.inl ⟨i,hi.symm⟩
  · exact Or.inr ⟨i,hi.symm⟩

def bondExistsInfinite : Set BondConfig := {ω | ∃ x, (bondCluster ω x).Infinite}
def siteExistsInfinite : Set SiteConfig := {ω | ∃ x, (siteCluster ω x).Infinite}

theorem measurableSet_bondExistsInfinite : MeasurableSet bondExistsInfinite := by
  simpa only [bondExistsInfinite,bondInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_bondInfiniteAt x))

theorem measurableSet_siteExistsInfinite : MeasurableSet siteExistsInfinite := by
  simpa only [siteExistsInfinite,siteInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_siteInfiniteAt x))

theorem bondExistsInfinite_of_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ bondExistsInfinite) :
    ω' ∈ bondExistsInfinite := by
  let F : Set Vertex := ((fun e : Bond => e.1) '' (J : Set Bond)) ∪
    ((fun e : Bond => step e.1 e.2) '' (J : Set Bond))
  have hF : F.Finite := (J.finite_toSet.image _).union (J.finite_toSet.image _)
  apply infinite_component_of_perturbation hF (s := BondOpen ω') (r := BondOpen ω) _ hω
  intro a b hab
  rcases hab with ⟨i,hb,hi⟩ | ⟨i,ha,hi⟩
  · by_cases hj : (a,i) ∈ J
    · exact Or.inr (Or.inr ⟨(a,i),hj,hb.symm⟩)
    · exact Or.inl (Or.inl ⟨i,hb,(hagree (a,i) hj).trans hi⟩)
  · by_cases hj : (b,i) ∈ J
    · exact Or.inr (Or.inl ⟨(b,i),hj,rfl⟩)
    · exact Or.inl (Or.inr ⟨i,ha,(hagree (b,i) hj).trans hi⟩)

theorem bondExistsInfinite_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ bondExistsInfinite ↔ ω ∈ bondExistsInfinite :=
  ⟨bondExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    bondExistsInfinite_of_finite_alteration J hagree⟩

theorem siteOpen_open_left {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    ω x = true := h.2.1

theorem siteOpen_open_right {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    ω y = true := h.2.2

theorem siteRtg_from_closed {ω : SiteConfig} {x y : Vertex} (hx : ω x ≠ true)
    (h : Relation.ReflTransGen (SiteOpen ω) x y) : y = x := by
  induction h with
  | refl => rfl
  | @tail a b _ hab ih =>
    exact (hx (ih ▸ siteOpen_open_left hab)).elim

theorem siteInfinite_iff_rtg_infinite (ω : SiteConfig) (x : Vertex) :
    (siteCluster ω x).Infinite ↔ {y | Relation.ReflTransGen (SiteOpen ω) x y}.Infinite := by
  by_cases hx : ω x = true
  · simp only [siteCluster,SiteConnected,hx,true_and]
  · have he : {y | Relation.ReflTransGen (SiteOpen ω) x y} = {x} := by
      ext y
      exact ⟨siteRtg_from_closed hx, fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact .refl⟩
    simp [siteCluster,SiteConnected,hx,he]

theorem siteExistsInfinite_of_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ siteExistsInfinite) :
    ω' ∈ siteExistsInfinite := by
  let F : Set Vertex := (J : Set Vertex) ∪ ⋃ x ∈ (J : Set Vertex), {y | NearestNeighbor x y}
  have hF : F.Finite := J.finite_toSet.union
    (J.finite_toSet.biUnion (fun x _ => finite_neighbors x))
  have hh : ∀ a b, SiteOpen ω a b → SiteOpen ω' a b ∨ b ∈ F := by
    intro a b hab
    by_cases ha : a ∈ J
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨a,ha,hab.1⟩))
    by_cases hb : b ∈ J
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ⟨hab.1,(hagree a ha).trans hab.2.1,(hagree b hb).trans hab.2.2⟩
  obtain ⟨x,hx⟩ := hω
  obtain ⟨y,hy⟩ := infinite_component_of_perturbation hF hh
    ⟨x,(siteInfinite_iff_rtg_infinite ω x).mp hx⟩
  exact ⟨y,(siteInfinite_iff_rtg_infinite ω' y).mpr hy⟩

theorem siteExistsInfinite_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ siteExistsInfinite ↔ ω ∈ siteExistsInfinite :=
  ⟨siteExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    siteExistsInfinite_of_finite_alteration J hagree⟩

open Filter
open scoped Topology

/-- Kolmogorov zero-one law in the finite-alteration form needed here. This
is proved for arbitrary independent bit coordinates, not assumed for clusters. -/
theorem zero_one_of_finite_alteration {E : Type uE} (μ : Measure (E → Bool))
    (hi : iIndepFun (fun e (ω : E → Bool) => ω e) μ)
    (A : Set (E → Bool)) (hA : MeasurableSet A)
    (hinv : ∀ (J : Finset E) (ω ω' : E → Bool),
      (∀ e ∉ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : μ A = 0 ∨ μ A = 1 := by
  classical
  let M : E → MeasurableSpace (E → Bool) :=
    fun e => MeasurableSpace.comap (fun ω => ω e) inferInstance
  have hM : ∀ e, M e ≤ (inferInstance : MeasurableSpace (E → Bool)) := fun e => (measurable_pi_apply e).comap_le
  have hmi : iIndep M μ := (iIndepFun_iff_iIndep _ _ _).mp hi
  have htail : MeasurableSet[limsup M cofinite] A := by
    rw [Filter.limsup_eq_iInf_iSup]
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro hs
    have hc : sᶜ.Finite := Filter.mem_cofinite.mp hs
    let f : (E → Bool) → (E → Bool) := fun ω e => if e ∈ s then ω e else false
    have hf : @Measurable (E → Bool) (E → Bool) (⨆ e ∈ s, M e) inferInstance f := by
      apply @measurable_pi_lambda (E → Bool) E (fun _ => Bool) (⨆ e ∈ s, M e) _ f
      intro e
      by_cases he : e ∈ s
      · simp only [f,ite_eq_left he]
        exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
      · simp only [f,ite_eq_right he]
        exact measurable_const
    have heq : f ⁻¹' A = A := by
      ext ω
      apply hinv hc.toFinset ω (f ω)
      intro e he
      have hes : e ∈ s := by simpa only [Set.Finite.mem_toFinset,Set.mem_compl_iff,not_not] using he
      simp only [f,ite_eq_left hes]
    rw [← heq]
    exact hf hA
  apply measure_zero_or_one_of_measurableSet_limsup hM hmi
    (p := fun s : Set E => s.Finite) (ns := fun J : Finset E => (J : Set E))
    (fun s hs => Filter.mem_cofinite.mpr (by simpa only [compl_compl] using hs)) _
    (fun J => J.finite_toSet) (fun e => ⟨{e},by simp⟩) htail
  intro J K
  exact ⟨J ∪ K, by simp, by simp⟩

theorem bondExistsInfinite_zero_one (p : ℝ) :
    bondLaw p bondExistsInfinite = 0 ∨ bondLaw p bondExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (bondLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    bondExistsInfinite measurableSet_bondExistsInfinite
  intro J ω ω' h
  exact bondExistsInfinite_finite_alteration J h

theorem siteExistsInfinite_zero_one (p : ℝ) :
    siteLaw p siteExistsInfinite = 0 ∨ siteLaw p siteExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (siteLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    siteExistsInfinite measurableSet_siteExistsInfinite
  intro J ω ω' h
  exact siteExistsInfinite_finite_alteration J h

theorem bondExistsInfinite_one {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) :
    bondLaw p bondExistsInfinite = 1 := by
  apply (bondExistsInfinite_zero_one p).resolve_left
  have h : 0 < bondLaw p bondExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

theorem siteExistsInfinite_one {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) :
    siteLaw p siteExistsInfinite = 1 := by
  apply (siteExistsInfinite_zero_one p).resolve_left
  have h : 0 < siteLaw p siteExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

def cube (c : Vertex) (n : ℕ) : Set Vertex :=
  Set.Icc (fun i => c i - (n : ℤ)) (fun i => c i + (n : ℤ))

theorem mem_cube {c x : Vertex} {n : ℕ} :
    x ∈ cube c n ↔ ∀ i, c i - (n : ℤ) ≤ x i ∧ x i ≤ c i + (n : ℤ) := by
  simp only [cube,Set.mem_Icc,Pi.le_def,forall_and]

theorem cube_finite (c : Vertex) (n : ℕ) : (cube c n).Finite := Set.finite_Icc _ _

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

theorem exists_mem_cube (c x : Vertex) : ∃ n, x ∈ cube c n := by
  let n := Finset.univ.sup (fun i : Fin 3 => (x i - c i).natAbs)
  refine ⟨n,mem_cube.mpr (fun i => ?_)⟩
  have hn : ((x i - c i).natAbs : ℤ) ≤ n := by
    exact_mod_cast (Finset.le_sup (f := fun i : Fin 3 => (x i - c i).natAbs) (Finset.mem_univ i))
  have hu := Int.le_natAbs (a := x i - c i)
  have hl := Int.le_natAbs (a := -(x i - c i))
  simp only [Int.natAbs_neg] at hl
  constructor <;> omega

@[simp] theorem iUnion_cube (c : Vertex) : (⋃ n, cube c n) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact exists_mem_cube c x

def bondSeedInfinite (c : Vertex) (n : ℕ) : Set BondConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ bondInfiniteAt x}
def siteSeedInfinite (c : Vertex) (n : ℕ) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c n, ω ∈ siteInfiniteAt x}

theorem bondSeedInfinite_mono (c : Vertex) : Monotone (bondSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩
theorem siteSeedInfinite_mono (c : Vertex) : Monotone (siteSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩

theorem measurableSet_bondSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (bondSeedInfinite c n) := by
  simp only [bondSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_bondInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]
theorem measurableSet_siteSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (siteSeedInfinite c n) := by
  simp only [siteSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_siteInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]

theorem iUnion_bondSeedInfinite (c : Vertex) :
    (⋃ n, bondSeedInfinite c n) = bondExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,bondSeedInfinite,bondExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩
theorem iUnion_siteSeedInfinite (c : Vertex) :
    (⋃ n, siteSeedInfinite c n) = siteExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,siteSeedInfinite,siteExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩

theorem bondSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < bondLaw p (bondInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => bondLaw p (bondSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := bondLaw p) (bondSeedInfinite_mono c)
  simpa only [iUnion_bondSeedInfinite,bondExistsInfinite_one hp,Function.comp_def] using h

theorem siteSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < siteLaw p (siteInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => siteLaw p (siteSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := siteLaw p) (siteSeedInfinite_mono c)
  simpa only [iUnion_siteSeedInfinite,siteExistsInfinite_one hp,Function.comp_def] using h

/-- The closed-cube vertex boundary used by the finite-scale argument. -/
def cubeBoundary (c : Vertex) (n : ℕ) : Set Vertex :=
  {x | x ∈ cube c n ∧ ∃ i, x i = c i - (n : ℤ) ∨ x i = c i + (n : ℤ)}

def Within {V : Type uV} (D : Set V) (r : V → V → Prop) (x y : V) : Prop :=
  x ∈ D ∧ y ∈ D ∧ r x y

theorem rtg_first_exit {V : Type uV} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
  have hh : ∀ {z}, Relation.ReflTransGen r x z →
      (z ∈ D ∧ Relation.ReflTransGen (Within D r) x z) ∨
      ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by
    intro z hz
    induction hz with
    | refl => exact Or.inl ⟨hx,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : b ∈ D
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
        · exact Or.inr ⟨a,ha,b,hb,hi,hab⟩
      · exact Or.inr he
  exact (hh h).resolve_left (fun h => hy h.1)

theorem nearestNeighbor_exit_boundary {c x y : Vertex} {n : ℕ}
    (hx : x ∈ cube c n) (hy : y ∉ cube c n) (hxy : NearestNeighbor x y) :
    x ∈ cubeBoundary c n := by
  refine ⟨hx,?_⟩
  rw [mem_cube] at hx hy
  push Not at hy
  obtain ⟨i,hi⟩ := hy
  obtain ⟨k,hk | hk⟩ := hxy
  · subst y
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inr ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hi
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hi
      omega
  · subst x
    by_cases hki : k = i
    · subst k
      refine ⟨i,Or.inl ?_⟩
      have hxi := hx i
      simp only [step,ite_true] at hxi ⊢
      omega
    · have hxi := hx i
      simp only [step,ite_eq_right hki,add_zero] at hxi
      omega

theorem bondOpen_neighbor {ω : BondConfig} {x y : Vertex} (h : BondOpen ω x y) :
    NearestNeighbor x y := by
  rcases h with ⟨i,hi,_⟩ | ⟨i,hi,_⟩
  · exact ⟨i,Or.inl hi⟩
  · exact ⟨i,Or.inr hi⟩

def bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set BondConfig :=
  {ω | ∃ x ∈ cube c m, ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (BondOpen ω)) x y}
def siteSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) : Set SiteConfig :=
  {ω | ∃ x ∈ cube c m, ω x = true ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c n) (SiteOpen ω)) x y}

/-- An infinite component supplies a finite path to the cube boundary;
this uses no uniqueness or unproved infinite-path theorem. -/
theorem bondSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    bondSeedInfinite c m ⊆ bondSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬bondCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,a,nearestNeighbor_exit_boundary ha hb (bondOpen_neighbor hab),hpath⟩

theorem siteSeedInfinite_subset_reachesBoundary (c : Vertex) {m n : ℕ} (hmn : m ≤ n) :
    siteSeedInfinite c m ⊆ siteSeedReaches c m n (cubeBoundary c n) := by
  rintro ω ⟨x,hxm,hx⟩
  have hnot : ¬siteCluster ω x ⊆ cube c n := fun h => hx ((cube_finite c n).subset h)
  obtain ⟨y,hy,hyn⟩ := Set.not_subset.mp hnot
  obtain ⟨a,ha,b,hb,hpath,hab⟩ := rtg_first_exit hy.2 (cube_mono c hmn hxm) hyn
  exact ⟨x,hxm,hy.1,a,nearestNeighbor_exit_boundary ha hb hab.1,hpath⟩

end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
open MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
variable {E F : Type u}

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.infinitePi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law; infer_instance

noncomputable def finiteLaw (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) : Measure (J → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance finiteLaw_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (finiteLaw J p) := by unfold finiteLaw; infer_instance

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem cylinder_integral (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (f : (J → Bool) → ℝ) :
    (∫ ω, f (J.restrict ω) ∂law p) = ∫ ξ,f ξ ∂finiteLaw J p := by
  rw [←map_restrict]
  exact (integral_map (Finset.measurable_restrict _).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable).symm

noncomputable def extend (J : Finset E) (ξ : J → Bool) : E → Bool :=
  fun e => if h : e ∈ J then ξ ⟨e,h⟩ else false

def DeterminedBy (J : Finset E) (f : (E → Bool) → F) : Prop :=
  ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

theorem measurableSet_determined (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : MeasurableSet A := by
  have he : A = J.restrict ⁻¹' {ξ | extend J ξ ∈ A} := by
    ext ω
    exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

theorem map_reindex (e : E ≃ F) (p : F → Set.Icc (0 : ℝ) 1) :
    (law p).map (fun ω i => ω (e i)) = law (fun i => p (e i)) := by
  have h := Measure.infinitePi_map_piCongrLeft
    (fun i => bernoulliMeasure true false (p (e i))) e.symm
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : E => Bool) e.symm) : (F → Bool) → E → Bool) =
      fun ω i => ω (e i) := by
    funext ω i
    change Equiv.piCongrLeft (fun _ : E => Bool) e.symm ω i = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [law,Equiv.apply_symm_apply,he] using h

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
open MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
variable {E : Type u}

noncomputable def law [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (law p) := by unfold law; infer_instance

noncomputable def mean [Fintype E] (p : E → Set.Icc (0 : ℝ) 1) (f : (E → Bool) → ℝ) : ℝ :=
  ∫ ω, f ω ∂law p

def extend (ω : E → Bool) (b : Bool) : Option E → Bool
  | none => b
  | some e => ω e

theorem extend_mono (b : Bool) : Monotone (fun ω : E → Bool => extend ω b) := by
  intro ω ω' h e
  cases e with
  | none => exact le_rfl
  | some e => exact h e

theorem extend_false_le_true (ω : E → Bool) : extend ω false ≤ extend ω true := by
  intro e
  cases e with
  | none => exact Bool.false_le _
  | some e => exact le_rfl

theorem mean_mono [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {f g : (E → Bool) → ℝ} (h : ∀ ω, f ω ≤ g ω) : mean p f ≤ mean p g :=
  integral_mono Integrable.of_finite Integrable.of_finite h

theorem mean_option [Fintype E] (p : Option E → Set.Icc (0 : ℝ) 1)
    (f : (Option E → Bool) → ℝ) :
    mean p f = (p none : ℝ) * mean (fun e => p (some e)) (fun ω => f (extend ω true)) +
      (1 - (p none : ℝ)) * mean (fun e => p (some e)) (fun ω => f (extend ω false)) := by
  unfold mean law
  rw [← Measure.pi_map_piOptionEquivProd (fun i => bernoulliMeasure true false (p i))]
  rw [integral_map (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm.measurable.aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_prod _ Integrable.of_finite]
  have heq : ∀ ω b, (MeasurableEquiv.piOptionEquivProd (fun _ : Option E => Bool)).symm (ω,b) =
      extend ω b := by
    intro ω b
    funext e
    cases e <;> rfl
  simp_rw [heq,integral_bernoulliMeasure,smul_eq_mul]
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul, integral_const_mul]

theorem mean_equiv {F : Type uF} [Fintype E] [Fintype F] (e : E ≃ F)
    (p : F → Set.Icc (0 : ℝ) 1) (f : (F → Bool) → ℝ) :
    mean p f = mean (fun a => p (e a)) (fun ω => f (fun b => ω (e.symm b))) := by
  have h := (measurePreserving_piCongrLeft (fun b => bernoulliMeasure true false (p b)) e).integral_comp
    (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e).measurableEmbedding f
  have he : ∀ ω, (MeasurableEquiv.piCongrLeft (fun _ : F => Bool) e) ω =
      fun b => ω (e.symm b) := by
    intro ω
    funext b
    change Equiv.piCongrLeft (fun _ : F => Bool) e ω b = ω (e.symm b)
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [mean,law,he,Function.comp_def] using h.symm

/-- Finite product positive association for arbitrary real increasing observables. -/
theorem increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h : ∀ (E : Type u) [Fintype E], ∀ (p : E → Set.Icc (0 : ℝ) 1)
      (f g : (E → Bool) → ℝ), Monotone f → Monotone g →
      mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
    apply Fintype.induction_empty_option
    · intro E F _ e ih p f g hf hg
      let _ : Fintype E := Fintype.ofEquiv F e.symm
      simp only [mean_equiv e p]
      apply ih
      · intro ω ω' h
        exact hf (fun b => h (e.symm b))
      · intro ω ω' h
        exact hg (fun b => h (e.symm b))
    · intro p f g _ _
      have heq (f : (PEmpty.{u+1} → Bool) → ℝ) : f = fun _ => f (fun x => x.elim) := by
        funext ω
        exact congrArg f (Subsingleton.elim _ _)
      rw [heq f,heq g]
      simp [mean]
    · intro E _ ih p f g hf hg
      let p' := fun e => p (some e)
      let f₀ := fun ω => f (extend ω false)
      let f₁ := fun ω => f (extend ω true)
      let g₀ := fun ω => g (extend ω false)
      let g₁ := fun ω => g (extend ω true)
      have h₀ := ih p' f₀ g₀ (hf.comp (extend_mono false)) (hg.comp (extend_mono false))
      have h₁ := ih p' f₁ g₁ (hf.comp (extend_mono true)) (hg.comp (extend_mono true))
      have hfm : mean p' f₀ ≤ mean p' f₁ := mean_mono p' (fun ω => hf (extend_false_le_true ω))
      have hgm : mean p' g₀ ≤ mean p' g₁ := mean_mono p' (fun ω => hg (extend_false_le_true ω))
      have hq0 : 0 ≤ (p none : ℝ) := (p none).2.1
      have hq1 : 0 ≤ 1 - (p none : ℝ) := sub_nonneg.mpr (p none).2.2
      have hc : 0 ≤ (p none : ℝ) * (1 - (p none : ℝ)) *
          (mean p' f₁ - mean p' f₀) * (mean p' g₁ - mean p' g₀) := by positivity
      have hsum := add_le_add (mul_le_mul_of_nonneg_left h₁ hq0) (mul_le_mul_of_nonneg_left h₀ hq1)
      simp only [mean_option]
      change ((p none : ℝ) * mean p' f₁ + (1 - (p none : ℝ)) * mean p' f₀) *
        ((p none : ℝ) * mean p' g₁ + (1 - (p none : ℝ)) * mean p' g₀) ≤
        (p none : ℝ) * mean p' (fun ω => f₁ ω * g₁ ω) +
        (1 - (p none : ℝ)) * mean p' (fun ω => f₀ ω * g₀ ω)
      nlinarith
  exact h E p f g hf hg

/-- Harris association also holds for decreasing observables. -/
theorem decreasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (f g : (E → Bool) → ℝ) (hf : Antitone f) (hg : Antitone g) :
    mean p f * mean p g ≤ mean p (fun ω => f ω * g ω) := by
  have h := increasing p (fun ω => -f ω) (fun ω => -g ω) hf.neg hg.neg
  simpa only [mean,integral_neg,neg_mul_neg] using h

noncomputable def prob [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : ℝ := mean p (fun ω => if P ω then 1 else 0)

theorem prob_nonneg [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : 0 ≤ prob p P := integral_nonneg (by intro ω; dsimp; split_ifs <;> norm_num)

theorem prob_eq_real [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : prob p P = (law p).real {ω | P ω} := by
  simpa [prob,mean,Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

theorem indicator_antitone {P : (E → Bool) → Prop} (hP : Antitone P) :
    Antitone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω'
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Antitone P) (hQ : Antitone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := decreasing p _ _ (indicator_antitone hP) (indicator_antitone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]

/-- The finite-family decreasing-event Harris inequality used for 24 quarter-faces. -/
theorem prob_forall [Fintype E] {I : Type uI} (p : E → Set.Icc (0 : ℝ) 1)
    (s : Finset I) (P : I → (E → Bool) → Prop) (hP : ∀ i ∈ s, Antitone (P i)) :
    (∏ i ∈ s, prob p (P i)) ≤ prob p (fun ω => ∀ i ∈ s, P i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prob,mean]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hs : ∀ j ∈ s, Antitone (P j) := fun j hj => hP j (Finset.mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left (ih hs) (prob_nonneg p (P i))
    refine h.trans ?_
    have hh := prob_and p (hP i (Finset.mem_insert_self i s))
      (fun ω ω' h h' j hj => hs j hj h (h' j hj))
    simpa only [Finset.mem_insert,forall_eq_or_imp] using hh

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

theorem extend_mono (J : Finset E) : Monotone (extend J) := by
  intro ξ ζ h e
  by_cases he : e ∈ J
  · simp only [extend, dite_eq_left he]
    exact h ⟨e,he⟩
  · simp only [extend, dite_eq_right he, le_refl]

/-- Harris's finite-family inequality, applied to actual infinite-product cylinder events. -/
theorem decreasing_forall {I : Type uI} [Fintype I] (J : Finset E)
    (p : E → Set.Icc (0 : ℝ) 1) (A : I → Set (E → Bool))
    (hA : ∀ i ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A i ↔ ω ∈ A i))
    (hmono : ∀ i, Antitone (fun ω => ω ∈ A i)) :
    (∏ i, (law p).real (A i)) ≤ (law p).real (⋂ i, A i) := by
  have he (i : I) : (law p).real (A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p (A i) (hA i)]
    rfl
  have hall : (law p).real (⋂ i, A i) =
      FiniteAssociation.prob (fun e : J => p e) (fun ξ => ∀ i, extend J ξ ∈ A i) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def]
    have hd : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ ⋂ i, A i ↔ ω ∈ ⋂ i, A i) := by
      intro ω ω' h
      simp only [Set.mem_iInter]
      exact forall_congr' (fun i => hA i ω ω' h)
    rw [probability_determined J p (⋂ i,A i) hd]
    simp only [Set.mem_iInter]
    rfl
  rw [hall]
  simp_rw [he]
  simpa only [Finset.mem_univ,forall_true_left] using
    FiniteAssociation.prob_forall (fun e : J => p e) Finset.univ
      (fun i ξ => extend J ξ ∈ A i) (fun i _ => (hmono i).comp_monotone (extend_mono J))

/-- The finite law is a polynomial in its bit parameters. -/
theorem finite_mass (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) (ξ : J → Bool) :
    (finiteLaw J p).real {ξ} = ∏ e : J, if ξ e = true then (p e : ℝ) else 1-(p e : ℝ) := by
  rw [Measure.real_def,finiteLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ξ e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases ξ e <;> simp [unitInterval.coe_symm_eq]

theorem continuous_probability (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    Continuous (fun p : E → Set.Icc (0 : ℝ) 1 => (law p).real A) := by
  have he (p : E → Set.Icc (0 : ℝ) 1) : (law p).real A =
      ∑ ξ : J → Bool, (∏ e : J, if ξ e then (p e : ℝ) else 1-(p e : ℝ)) *
        (if extend J ξ ∈ A then 1 else 0) := by
    rw [Measure.real_def,probability_determined J p A hA]
    change (finiteLaw J p).real {ξ | extend J ξ ∈ A} = _
    rw [←integral_indicator_one (Set.toFinite _).measurableSet]
    rw [integral_fintype (Integrable.of_finite)]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [finite_mass]
    simp [Set.indicator,smul_eq_mul]
  simp_rw [he]
  apply continuous_finsetSum
  intro ξ _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  cases ξ e
  · exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply e.val))
  · exact continuous_subtype_val.comp (continuous_apply e.val)

end ProductCylinder

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

noncomputable def internalSites (D : Set Vertex) (hD : D.Finite) : Finset Vertex := hD.toFinset
noncomputable def internalBonds (D : Set Vertex) (hD : D.Finite) : Finset Bond :=
  (hD.toFinset ×ˢ Finset.univ).filter (fun e => step e.1 e.2 ∈ D)

theorem mem_internalBonds {D : Set Vertex} {hD : D.Finite} {e : Bond} :
    e ∈ internalBonds D hD ↔ e.1 ∈ D ∧ step e.1 e.2 ∈ D := by
  simp [internalBonds]

theorem bondWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : BondConfig}
    (hω : ∀ e ∈ internalBonds D hD, ω' e = ω e) :
    Within D (BondOpen ω') = Within D (BondOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,BondOpen]
    apply or_congr
    · apply exists_congr
      intro i
      by_cases he : y = step x i
      · rw [hω (x,i) (mem_internalBonds.mpr ⟨hx,he ▸ hy⟩)]
      · simp [he]
    · apply exists_congr
      intro i
      by_cases he : x = step y i
      · rw [hω (y,i) (mem_internalBonds.mpr ⟨hy,he ▸ hx⟩)]
      · simp [he]
  all_goals simp [Within,hx,hy]

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem siteSeedReaches_determined (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ (cube_finite c n).toFinset, ω' e = ω e) →
      (ω' ∈ siteSeedReaches c m n T ↔ ω ∈ siteSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [siteSeedReaches,Set.mem_ofPred_eq,siteWithin_congr hω]
  apply exists_congr
  intro x
  by_cases hx : x ∈ cube c m
  · simp only [hx,true_and,hω x ((cube_finite c n).mem_toFinset.mpr (cube_mono c hmn hx))]
  · simp only [hx,false_and]

theorem bondOpen_mono {ω ω' : BondConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : BondOpen ω x y) : BondOpen ω' x y := by
  rcases hxy with ⟨i,hi,hw⟩ | ⟨i,hi,hw⟩
  · exact Or.inl ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (x,i))⟩
  · exact Or.inr ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (y,i))⟩

theorem siteOpen_mono {ω ω' : SiteConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : SiteOpen ω x y) : SiteOpen ω' x y :=
  ⟨hxy.1,Bool.eq_true_of_true_le (hxy.2.1 ▸ h x),Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)⟩

theorem bondSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ bondSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,y,hy,hp⟩
  refine ⟨x,hx,y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,bondOpen_mono h h'.2.2⟩

theorem siteSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ siteSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,hω,y,hy,hp⟩
  refine ⟨x,hx,Bool.eq_true_of_true_le (hω ▸ h x),y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,siteOpen_mono h h'.2.2⟩

end CriticalZ3

namespace CriticalZ3
open Classical

structure SignedSymmetry where
  perm : Equiv.Perm (Fin 3)
  signs : Fin 3 → Bool
  shift : Vertex

namespace SignedSymmetry

def vertex (S : SignedSymmetry) : Vertex ≃ Vertex where
  toFun x := fun i => S.shift i + if S.signs i then x (S.perm i) else -x (S.perm i)
  invFun y := fun i => if S.signs (S.perm.symm i) then
    y (S.perm.symm i)-S.shift (S.perm.symm i) else -(y (S.perm.symm i)-S.shift (S.perm.symm i))
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases S.signs (S.perm.symm i) <;> simp
  right_inv y := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases S.signs i <;> simp

def edgeShift (S : SignedSymmetry) (k : Fin 3) : Vertex :=
  fun i => if S.signs (S.perm.symm k) then 0 else if S.perm.symm k = i then -1 else 0

def bond (S : SignedSymmetry) : Bond ≃ Bond :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongrRight (fun k => S.vertex.trans (Equiv.addRight (S.edgeShift k)))).trans
    ((Equiv.prodCongr S.perm.symm (Equiv.refl _)).trans (Equiv.prodComm _ _)))

theorem bond_apply (S : SignedSymmetry) (e : Bond) :
    S.bond e = (S.vertex e.1+S.edgeShift e.2,S.perm.symm e.2) := rfl

theorem edge_spec (S : SignedSymmetry) (e : Bond) :
    (S.vertex e.1 = (S.bond e).1 ∧ S.vertex (step e.1 e.2) = step (S.bond e).1 (S.bond e).2) ∨
    (S.vertex e.1 = step (S.bond e).1 (S.bond e).2 ∧ S.vertex (step e.1 e.2) = (S.bond e).1) := by
  have hi (i : Fin 3) : (e.2 = S.perm i) ↔ (S.perm.symm e.2 = i) := by
    constructor
    · intro h; rw [h,Equiv.symm_apply_apply]
    · intro h; rw [←h,Equiv.apply_symm_apply]
  by_cases hs : S.signs (S.perm.symm e.2) = true
  · left
    constructor
    · funext i
      simp [bond_apply,edgeShift,hs]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i = true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]
  · right
    constructor
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,he]
      · simp [bond_apply,vertex,edgeShift,step,hs,he]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]

def Endpoints (e : Bond) (x y : Vertex) : Prop :=
  (x = e.1 ∧ y = step e.1 e.2) ∨ (y = e.1 ∧ x = step e.1 e.2)

theorem endpoints_map (S : SignedSymmetry) (e : Bond) (x y : Vertex) :
    Endpoints (S.bond e) (S.vertex x) (S.vertex y) ↔ Endpoints e x y := by
  rcases S.edge_spec e with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · unfold Endpoints
    rw [←h₂,←h₁]
    simp only [Equiv.apply_eq_iff_eq]
  · unfold Endpoints
    rw [←h₁,←h₂]
    simp only [Equiv.apply_eq_iff_eq]
    tauto

theorem bondOpen_iff (ω : BondConfig) (x y : Vertex) :
    BondOpen ω x y ↔ ∃ e, ω e = true ∧ Endpoints e x y := by
  constructor
  · rintro (⟨i,h,hω⟩ | ⟨i,h,hω⟩)
    · exact ⟨(x,i),hω,Or.inl ⟨rfl,h⟩⟩
    · exact ⟨(y,i),hω,Or.inr ⟨rfl,h⟩⟩
  · rintro ⟨⟨z,i⟩,hω,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ⟨i,rfl,hω⟩
    · exact Or.inr ⟨i,rfl,hω⟩

theorem bondOpen_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondOpen (fun e => ω (S.bond e)) x y ↔ BondOpen ω (S.vertex x) (S.vertex y) := by
  simp_rw [bondOpen_iff]
  constructor
  · rintro ⟨e,he,hxy⟩
    exact ⟨S.bond e,he,(S.endpoints_map e x y).mpr hxy⟩
  · rintro ⟨e,he,hxy⟩
    refine ⟨S.bond.symm e,by simpa using he,?_⟩
    apply (S.endpoints_map (S.bond.symm e) x y).mp
    simpa using hxy

theorem neighbor_map (S : SignedSymmetry) (x y : Vertex) :
    NearestNeighbor x y ↔ NearestNeighbor (S.vertex x) (S.vertex y) := by
  have he (x y : Vertex) : NearestNeighbor x y ↔ BondOpen (fun _ => true) x y := by
    simp only [NearestNeighbor,BondOpen,and_true]
    rw [exists_or]
  simpa only [he] using S.bondOpen_map (fun _ => true) x y

theorem siteOpen_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteOpen (fun e => ω (S.vertex e)) x y ↔ SiteOpen ω (S.vertex x) (S.vertex y) := by
  simp only [SiteOpen,←S.neighbor_map]

theorem cube_map (S : SignedSymmetry) (c x : Vertex) (n : ℕ) :
    x ∈ cube c n ↔ S.vertex x ∈ cube (S.vertex c) n := by
  simp only [mem_cube]
  have he (i : Fin 3) :
      (S.vertex c i - (n:ℤ) ≤ S.vertex x i ∧ S.vertex x i ≤ S.vertex c i + (n:ℤ)) ↔
      (c (S.perm i)-(n:ℤ) ≤ x (S.perm i) ∧ x (S.perm i) ≤ c (S.perm i)+(n:ℤ)) := by
    dsimp [vertex]
    cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [he]
  constructor
  · intro h i; exact h _
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)

end SignedSymmetry
end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

abbrev FaceIndex := Fin 3 × (Fin 3 → Bool)

def QuarterFace (c : Vertex) (n : ℕ) (f : FaceIndex) : Set Vertex :=
  {x | x f.1 = c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ)) ∧
    ∀ i, i ≠ f.1 → if f.2 i then c i ≤ x i ∧ x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ x i ∧ x i ≤ c i}

def canonicalFace : FaceIndex := (0, fun _ => true)

theorem quarterFace_subset_boundary (c : Vertex) (n : ℕ) (f : FaceIndex) :
    QuarterFace c n f ⊆ cubeBoundary c n := by
  intro x hx
  refine ⟨?_,f.1,?_⟩
  · rw [mem_cube]
    intro i
    by_cases hi : i = f.1
    · subst i
      rw [hx.1]
      cases f.2 f.1 <;> simp
      omega
    · have h := hx.2 i hi
      cases hf : f.2 i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · rw [hx.1]
    cases f.2 f.1 <;> simp [sub_eq_add_neg]

theorem boundary_eq_union_quarterFace (c : Vertex) (n : ℕ) :
    cubeBoundary c n = ⋃ f : FaceIndex, QuarterFace c n f := by
  apply Set.Subset.antisymm
  · rintro x ⟨hx,i,hi⟩
    rw [Set.mem_iUnion]
    let signs : Fin 3 → Bool := fun j => decide (c j ≤ x j)
    refine ⟨(i,signs),?_,?_⟩
    · change x i = c i + (if signs i then (n : ℤ) else -(n : ℤ))
      by_cases h : c i ≤ x i <;> simp [signs,h]
      all_goals rcases hi with hi | hi <;> omega
    · intro j _
      have hh := (mem_cube.mp hx) j
      change if signs j then c j ≤ x j ∧ x j ≤ c j + (n : ℤ)
        else c j - (n : ℤ) ≤ x j ∧ x j ≤ c j
      by_cases h : c j ≤ x j <;> simp [signs,h]
      all_goals omega
  · exact Set.iUnion_subset (quarterFace_subset_boundary c n)

theorem rtg_equiv_iff {V : Type uV} {W : Type uW} (e : V ≃ W) {r : V → V → Prop} {s : W → W → Prop}
    (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : V) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · intro hp
    exact Relation.ReflTransGen.lift e (fun a b h' => (h a b).mp h') x y hp
  · intro hp
    have hp' := Relation.ReflTransGen.lift e.symm (fun a b h' =>
      (h (e.symm a) (e.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using h'))
      (e x) (e y) hp
    simpa only [Function.onFun,Equiv.symm_apply_apply] using hp'

namespace SignedSymmetry

theorem bondWithin_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (BondOpen (fun e => ω (S.bond e))) x y ↔
      Within (cube (S.vertex c) n) (BondOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.bondOpen_map]

theorem siteWithin_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (n : ℕ) (x y : Vertex) :
    Within (cube c n) (SiteOpen (fun e => ω (S.vertex e))) x y ↔
      Within (cube (S.vertex c) n) (SiteOpen ω) (S.vertex x) (S.vertex y) := by
  simp only [Within,S.cube_map c x n,S.cube_map c y n,S.siteOpen_map]

theorem bondSeedReaches_map (S : SignedSymmetry) (ω : BondConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.bond e)) ∈ bondSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ bondSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.bondWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

theorem siteSeedReaches_map (S : SignedSymmetry) (ω : SiteConfig) (c : Vertex) (m n : ℕ)
    (T : Set Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteSeedReaches c m n (S.vertex ⁻¹' T) ↔
      ω ∈ siteSeedReaches (S.vertex c) m n T := by
  change (∃ x ∈ cube c m, ω (S.vertex x) = true ∧ ∃ y, S.vertex y ∈ T ∧ _) ↔ _
  simp_rw [rtg_equiv_iff S.vertex (S.siteWithin_map ω c n)]
  constructor
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    exact ⟨S.vertex x,(S.cube_map c x m).mp hx,hw,S.vertex y,hy,hp⟩
  · rintro ⟨x,hx,hw,y,hy,hp⟩
    refine ⟨S.vertex.symm x,?_,?_,S.vertex.symm y,?_,?_⟩
    · exact (S.cube_map c _ m).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · simpa only [Equiv.apply_symm_apply] using hw
    · simpa only [Equiv.apply_symm_apply] using hy
    · simpa only [Equiv.apply_symm_apply] using hp

end SignedSymmetry

def faceSymmetry (c : Vertex) (f : FaceIndex) : SignedSymmetry :=
  ⟨Equiv.swap f.1 0, f.2, c⟩

@[simp] theorem faceSymmetry_zero (c : Vertex) (f : FaceIndex) :
    (faceSymmetry c f).vertex 0 = c := by
  funext i
  simp [faceSymmetry,SignedSymmetry.vertex]

theorem quarterFace_preimage (c : Vertex) (n : ℕ) (f : FaceIndex) :
    (faceSymmetry c f).vertex ⁻¹' QuarterFace c n f = QuarterFace 0 n canonicalFace := by
  ext x
  simp only [Set.mem_preimage,QuarterFace,Set.mem_ofPred_eq,canonicalFace,
    Pi.zero_apply,zero_add,ite_true]
  have hn : (faceSymmetry c f).vertex x f.1 =
      c f.1 + if f.2 f.1 then x 0 else -x 0 := by
    simp [faceSymmetry,SignedSymmetry.vertex]
  rw [hn]
  have hnormal : (c f.1 + (if f.2 f.1 then x 0 else -x 0) =
      c f.1 + (if f.2 f.1 then (n : ℤ) else -(n : ℤ))) ↔ x 0 = (n : ℤ) := by
    cases f.2 f.1 <;> simp
  rw [hnormal]
  apply and_congr_right
  intro _
  have hi (i : Fin 3) :
      (if f.2 i then c i ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ (faceSymmetry c f).vertex x i ∧
        (faceSymmetry c f).vertex x i ≤ c i) ↔
      (0 ≤ x (Equiv.swap f.1 0 i) ∧ x (Equiv.swap f.1 0 i) ≤ (n : ℤ)) := by
    change (if f.2 i then c i ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i + (n : ℤ)
      else c i - (n : ℤ) ≤ c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ∧
      c i + (if f.2 i then x (Equiv.swap f.1 0 i) else -x (Equiv.swap f.1 0 i)) ≤ c i) ↔ _
    cases f.2 i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  simp_rw [hi]
  constructor
  · intro h i hi
    have hh := h (Equiv.swap f.1 0 i)
    simp only [Equiv.swap_apply_self] at hh
    apply hh
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_left] at this
    exact hi this
  · intro h i hi
    apply h
    intro he
    have := congrArg (Equiv.swap f.1 0) he
    simp only [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
    exact hi this

end CriticalZ3

namespace ProductCylinder

theorem reindex_probability {E : Type uE} (e : E ≃ E) (p : Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    law (fun _ => p) ((fun ω i => ω (e i)) ⁻¹' A) = law (fun _ => p) A := by
  rw [←Measure.map_apply (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i))) hA,
    map_reindex]

end ProductCylinder

namespace CriticalZ3
open Classical

theorem measurableSet_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    MeasurableSet (bondSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (bondSeedReaches_determined c m n T)

theorem measurableSet_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    MeasurableSet (siteSeedReaches c m n T) :=
  ProductCylinder.measurableSet_determined _ _ (siteSeedReaches_determined c m n hmn T)

theorem bondQuarterFace_probability (p : ℝ) (c : Vertex) (m n : ℕ) (f : FaceIndex) :
    bondLaw p (bondSeedReaches c m n (QuarterFace c n f)) =
      bondLaw p (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace)) := by
  let S := faceSymmetry c f
  have hm := ProductCylinder.reindex_probability S.bond (parameter p)
    (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))
    (measurableSet_bondSeedReaches _ _ _ _)
  change bondLaw p _ = bondLaw p _ at hm
  rw [←hm]
  congr 1
  ext ω
  have h := S.bondSeedReaches_map ω 0 m n (QuarterFace c n f)
  simpa only [S,faceSymmetry_zero,quarterFace_preimage,Set.mem_preimage] using h.symm

theorem siteQuarterFace_probability (p : ℝ) (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (f : FaceIndex) :
    siteLaw p (siteSeedReaches c m n (QuarterFace c n f)) =
      siteLaw p (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace)) := by
  let S := faceSymmetry c f
  have hm := ProductCylinder.reindex_probability S.vertex (parameter p)
    (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))
    (measurableSet_siteSeedReaches _ _ _ hmn _)
  change siteLaw p _ = siteLaw p _ at hm
  rw [←hm]
  congr 1
  ext ω
  have h := S.siteSeedReaches_map ω 0 m n (QuarterFace c n f)
  simpa only [S,faceSymmetry_zero,quarterFace_preimage,Set.mem_preimage] using h.symm

theorem bondQuarterFace_compl_real (p : ℝ) (c : Vertex) (m n : ℕ) (f : FaceIndex) :
    (bondLaw p).real (bondSeedReaches c m n (QuarterFace c n f))ᶜ =
      (bondLaw p).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ := by
  rw [measureReal_compl (measurableSet_bondSeedReaches _ _ _ _),
    measureReal_compl (measurableSet_bondSeedReaches _ _ _ _)]
  simp only [Measure.real_def,bondQuarterFace_probability]

theorem siteQuarterFace_compl_real (p : ℝ) (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (f : FaceIndex) :
    (siteLaw p).real (siteSeedReaches c m n (QuarterFace c n f))ᶜ =
      (siteLaw p).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ := by
  rw [measureReal_compl (measurableSet_siteSeedReaches _ _ _ hmn _),
    measureReal_compl (measurableSet_siteSeedReaches _ _ _ hmn _)]
  simp only [Measure.real_def,siteQuarterFace_probability p c m n hmn]

theorem bondBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    bondSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, bondSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [bondSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,y,hf,hp⟩
  · rintro ⟨f,x,hx,y,hf,hp⟩
    exact ⟨x,hx,y,⟨f,hf⟩,hp⟩

theorem siteBoundary_eq_union_reachesFaces (c : Vertex) (m n : ℕ) :
    siteSeedReaches c m n (cubeBoundary c n) = ⋃ f : FaceIndex, siteSeedReaches c m n (QuarterFace c n f) := by
  ext ω
  simp only [siteSeedReaches,boundary_eq_union_quarterFace,Set.mem_iUnion,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩
    exact ⟨f,x,hx,hw,y,hf,hp⟩
  · rintro ⟨f,x,hx,hw,y,hf,hp⟩
    exact ⟨x,hx,hw,y,⟨f,hf⟩,hp⟩

theorem card_faceIndex : Fintype.card FaceIndex = 24 := by
  norm_num [FaceIndex,Fintype.card_prod,Fintype.card_fun]

theorem bondQuarterFace_Harris (p : ℝ) (m n : ℕ) :
    ((bondLaw p).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)^24 ≤
      (bondLaw p).real (bondSeedReaches 0 m n (cubeBoundary 0 n))ᶜ := by
  have h := ProductCylinder.decreasing_forall
    (internalBonds (cube 0 n) (cube_finite 0 n)) (fun _ => parameter p)
    (fun f : FaceIndex => (bondSeedReaches 0 m n (QuarterFace 0 n f))ᶜ)
    (fun f ω ω' hω => not_congr (bondSeedReaches_determined _ _ _ _ ω ω' hω))
    (fun f ω ω' hω h' h => h' (bondSeedReaches_mono _ _ _ _ hω h))
  change (∏ f : FaceIndex, (bondLaw p).real _) ≤ (bondLaw p).real _ at h
  simp_rw [bondQuarterFace_compl_real] at h
  simpa only [Finset.prod_const,Finset.card_univ,card_faceIndex,
    ←Set.compl_iUnion,←bondBoundary_eq_union_reachesFaces] using h

theorem siteQuarterFace_Harris (p : ℝ) (m n : ℕ) (hmn : m ≤ n) :
    ((siteLaw p).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)^24 ≤
      (siteLaw p).real (siteSeedReaches 0 m n (cubeBoundary 0 n))ᶜ := by
  have h := ProductCylinder.decreasing_forall
    (cube_finite 0 n).toFinset (fun _ => parameter p)
    (fun f : FaceIndex => (siteSeedReaches 0 m n (QuarterFace 0 n f))ᶜ)
    (fun f ω ω' hω => not_congr (siteSeedReaches_determined _ _ _ hmn _ ω ω' hω))
    (fun f ω ω' hω h' h => h' (siteSeedReaches_mono _ _ _ _ hω h))
  change (∏ f : FaceIndex, (siteLaw p).real _) ≤ (siteLaw p).real _ at h
  simp_rw [siteQuarterFace_compl_real p 0 m n hmn] at h
  simpa only [Finset.prod_const,Finset.card_univ,card_faceIndex,
    ←Set.compl_iUnion,←siteBoundary_eq_union_reachesFaces] using h

theorem bondQuarterFace_root_bound (p : ℝ) (m n : ℕ) (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hseed : (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < ε^24) (c : Vertex) (f : FaceIndex) :
    (bondLaw p).real (bondSeedReaches c m n (QuarterFace c n f))ᶜ < ε := by
  rw [bondQuarterFace_compl_real]
  apply (pow_lt_pow_iff_left₀ (measureReal_nonneg) hε (by norm_num : (24:ℕ) ≠ 0)).mp
  refine (bondQuarterFace_Harris p m n).trans_lt (lt_of_le_of_lt ?_ hseed)
  exact measureReal_mono (Set.compl_subset_compl.mpr (bondSeedInfinite_subset_reachesBoundary 0 hmn))

theorem siteQuarterFace_root_bound (p : ℝ) (m n : ℕ) (hmn : m ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hseed : (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < ε^24) (c : Vertex) (f : FaceIndex) :
    (siteLaw p).real (siteSeedReaches c m n (QuarterFace c n f))ᶜ < ε := by
  rw [siteQuarterFace_compl_real p c m n hmn]
  apply (pow_lt_pow_iff_left₀ (measureReal_nonneg) hε (by norm_num : (24:ℕ) ≠ 0)).mp
  refine (siteQuarterFace_Harris p m n hmn).trans_lt (lt_of_le_of_lt ?_ hseed)
  exact measureReal_mono (Set.compl_subset_compl.mpr (siteSeedInfinite_subset_reachesBoundary 0 hmn))

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

theorem bondSeedMiss_tendsto_zero {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun m => (bondLaw p).real (bondSeedInfinite c m)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp (bondSeedInfinite_tendsto_one hp c)
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa only [measureReal_compl (measurableSet_bondSeedInfinite c _),probReal_univ,
    Measure.real_def,measure_univ,ENNReal.toReal_one,sub_self,Function.comp_def] using h'

theorem siteSeedMiss_tendsto_zero {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun m => (siteLaw p).real (siteSeedInfinite c m)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp (siteSeedInfinite_tendsto_one hp c)
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa only [measureReal_compl (measurableSet_siteSeedInfinite c _),probReal_univ,
    Measure.real_def,measure_univ,ENNReal.toReal_one,sub_self,Function.comp_def] using h'

theorem exists_bondSeed {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < ε^24 := by
  have h := (bondSeedMiss_tendsto_zero hp 0).eventually (eventually_lt_nhds (pow_pos hε 24))
  exact (h.and (eventually_gt_atTop 0)).exists.imp (fun _ h => h.symm)

theorem exists_siteSeed {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < ε^24 := by
  have h := (siteSeedMiss_tendsto_zero hp 0).eventually (eventually_lt_nhds (pow_pos hε 24))
  exact (h.and (eventually_gt_atTop 0)).exists.imp (fun _ h => h.symm)

theorem continuous_parameter : Continuous parameter := by
  exact (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _

theorem continuous_bondSeedReaches (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (bondSeedReaches_determined c m n T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_siteSeedReaches (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)) :=
  (ProductCylinder.continuous_probability _ _ (siteSeedReaches_determined c m n hmn T)).comp
    (continuous_pi (fun _ => continuous_parameter))

theorem continuous_bondSeedMiss (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Continuous (fun p => (bondLaw p).real (bondSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_bondSeedReaches c m n T),probReal_univ]
  exact continuous_const.sub (continuous_bondSeedReaches _ _ _ _)

theorem continuous_siteSeedMiss (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    Continuous (fun p => (siteLaw p).real (siteSeedReaches c m n T)ᶜ) := by
  simp_rw [measureReal_compl (measurableSet_siteSeedReaches c m n hmn T),probReal_univ]
  exact continuous_const.sub (continuous_siteSeedReaches _ _ _ hmn _)

/-- A single strictly lower parameter preserves simultaneous finite strict bounds. -/
theorem exists_lower_forall {I : Type uI} [Finite I] {p γ : ℝ} (hp : 0 < p)
    (g : I → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (hgp : ∀ i, g i p < γ) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ i, g i q < γ := by
  have ho : IsOpen {q | ∀ i, g i q < γ} := by
    have he : {q | ∀ i, g i q < γ} = ⋂ i, (g i) ⁻¹' Set.Iio γ := by ext q; simp
    rw [he]
    exact isOpen_iInter_of_finite (fun i => isOpen_Iio.preimage (hg i))
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho p hgp
  let a : ℝ := min (p/4) (ε/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hap : a ≤ p/4 := min_le_left _ _
  have hae : a ≤ ε/2 := min_le_right _ _
  refine ⟨p-a,⟨by linarith,by linarith⟩,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos ha]
  linarith

/-- Quarter-face estimates at any fixed finite family of enclosing radii,
at one parameter below p, uniformly over every center and all 24 faces. -/
theorem bond_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (bondLaw q).real (bondSeedReaches c m n (QuarterFace c n f)) := by
  obtain ⟨q,hq,hfaces⟩ := exists_lower_forall hp
    (fun n : s => fun t => (bondLaw t).real (bondSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)
    (fun n => continuous_bondSeedMiss _ _ _ _) (fun n =>
      (bondQuarterFace_root_bound p m n (hs n n.property) (by positivity) hseed 0 canonicalFace).trans
        (by linarith : γ/2 < γ))
  refine ⟨q,hq,?_⟩
  intro n hn c f
  have h := hfaces ⟨n,hn⟩
  rw [←bondQuarterFace_compl_real q c m n f,
    measureReal_compl (measurableSet_bondSeedReaches _ _ _ _),probReal_univ] at h
  linarith

theorem site_lower_quarterFaces {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {m : ℕ} (hseed : (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, m ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (siteLaw q).real (siteSeedReaches c m n (QuarterFace c n f)) := by
  obtain ⟨q,hq,hfaces⟩ := exists_lower_forall hp
    (fun n : s => fun t => (siteLaw t).real (siteSeedReaches 0 m n (QuarterFace 0 n canonicalFace))ᶜ)
    (fun n => continuous_siteSeedMiss _ _ _ (hs n n.property) _) (fun n =>
      (siteQuarterFace_root_bound p m n (hs n n.property) (by positivity) hseed 0 canonicalFace).trans
        (by linarith : γ/2 < γ))
  refine ⟨q,hq,?_⟩
  intro n hn c f
  have h := hfaces ⟨n,hn⟩
  rw [←siteQuarterFace_compl_real q c m n (hs n hn) f,
    measureReal_compl (measurableSet_siteSeedReaches _ _ _ (hs n hn) _),probReal_univ] at h
  linarith

end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical

open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open scoped BigOperators Matrix
open Filter

namespace FiniteResampling
variable {I : Type uI} [Fintype I] [Nonempty I]

noncomputable def lower (f : I → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty f
noncomputable def upper (f : I → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

theorem lower_le (f : I → ℝ) (i : I) : lower f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)
theorem le_upper (f : I → ℝ) (i : I) : f i ≤ upper f :=
  Finset.le_sup' f (Finset.mem_univ i)
theorem le_lower {f : I → ℝ} {a : ℝ} (h : ∀ i, a ≤ f i) : a ≤ lower f :=
  Finset.le_inf' Finset.univ_nonempty f (fun i _ => h i)
theorem upper_le {f : I → ℝ} {a : ℝ} (h : ∀ i, f i ≤ a) : upper f ≤ a :=
  Finset.sup'_le Finset.univ_nonempty f (fun i _ => h i)
theorem lower_le_upper (f : I → ℝ) : lower f ≤ upper f := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (lower_le f i).trans (le_upper f i)

structure Transition (I : Type uI) [Fintype I] where
  weight : I → I → ℝ
  nonneg : ∀ i j, 0 ≤ weight i j
  total : ∀ i, ∑ j, weight i j = 1

namespace Transition
variable (K : Transition I)
noncomputable def act (f : I → ℝ) (i : I) : ℝ := ∑ j, K.weight i j * f j

omit [Nonempty I] in
theorem act_const (a : ℝ) (i : I) : K.act (fun _ => a) i = a := by
  simp [act, ← Finset.sum_mul, K.total]

omit [Nonempty I] in
theorem act_mono {f g : I → ℝ} (h : f ≤ g) : K.act f ≤ K.act g := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (K.nonneg i j))

theorem lower_le_act (f : I → ℝ) (i : I) : lower f ≤ K.act f i := by
  rw [← K.act_const (lower f) i]
  exact K.act_mono (fun j => lower_le f j) i

theorem act_le_upper (f : I → ℝ) (i : I) : K.act f i ≤ upper f := by
  rw [← K.act_const (upper f) i]
  exact K.act_mono (fun j => le_upper f j) i

theorem lower_le_lower_act (f : I → ℝ) : lower f ≤ lower (K.act f) :=
  le_lower (K.lower_le_act f)

theorem upper_act_le_upper (f : I → ℝ) : upper (K.act f) ≤ upper f :=
  upper_le (K.act_le_upper f)

/-- Subtracting the same atom from each row exposes a nonnegative remainder. -/
theorem common_atom_bounds (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) (i : I) :
    a * f z + (1-a) * lower f ≤ K.act f i ∧
      K.act f i ≤ a * f z + (1-a) * upper f := by
  classical
  let r : I → ℝ := fun j => K.weight i j - if j = z then a else 0
  have hr : ∀ j, 0 ≤ r j := by
    intro j
    dsimp [r]
    split_ifs with h
    · subst j; exact sub_nonneg.mpr (ha i)
    · simpa using K.nonneg i j
  have hsum : ∑ j, r j = 1-a := by simp [r, Finset.sum_sub_distrib, K.total]
  have heq : K.act f i = a * f z + ∑ j, r j * f j := by
    simp [act, r, sub_mul, Finset.sum_sub_distrib, ite_mul]
  rw [heq]
  constructor
  · apply add_le_add le_rfl
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (lower_le f j) (hr j))
  · apply add_le_add le_rfl
    rw [← hsum, Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (le_upper f j) (hr j))

theorem oscillation_contract (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) :
    upper (K.act f) - lower (K.act f) ≤ (1-a) * (upper f-lower f) := by
  have hl := le_lower (fun i => (K.common_atom_bounds z a ha f i).1)
  have hu := upper_le (fun i => (K.common_atom_bounds z a ha f i).2)
  nlinarith

/-- All finite transition iterates converge to a constant when every row shares
one positive atom. Zero-probability states are permitted and not discarded. -/
theorem iterates_tendsto_constant (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by
  let g : ℕ → I → ℝ := fun n => (K.act)^[n] f
  have hstep (n : ℕ) : g (n+1) = K.act (g n) := by
    exact Function.iterate_succ_apply' _ _ _
  have hl : Monotone (fun n => lower (g n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hstep]
    exact K.lower_le_lower_act _
  have hu : Antitone (fun n => upper (g n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hstep]
    exact K.upper_act_le_upper _
  have hbb : ∀ n, lower (g n) ≤ upper f := by
    intro n
    exact (lower_le_upper _).trans (hu (Nat.zero_le n))
  have hbdd : BddAbove (Set.range (fun n => lower (g n))) := by
    exact ⟨upper f, fun _ ⟨n, hn⟩ => hn ▸ hbb n⟩
  have hdelta : ∀ n, upper (g n)-lower (g n) ≤
      (1-a)^n * (upper f-lower f) := by
    intro n
    induction n with
    | zero => simp [g]
    | succ n ih =>
      calc
        upper (g (n+1))-lower (g (n+1)) ≤ (1-a) * (upper (g n)-lower (g n)) := by
          rw [hstep]
          exact K.oscillation_contract z a ha _
        _ ≤ (1-a) * ((1-a)^n * (upper f-lower f)) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ha1)
        _ = (1-a)^(n+1) * (upper f-lower f) := by ring
  have hdlim : Tendsto (fun n => upper (g n)-lower (g n)) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (lower_le_upper _)))
      (Filter.Eventually.of_forall hdelta)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha1)
      (by linarith : 1-a < 1)).mul_const (upper f-lower f)
  let c := ⨆ n, lower (g n)
  have hllim : Tendsto (fun n => lower (g n)) atTop (nhds c) :=
    tendsto_atTop_ciSup hl hbdd
  have hulim : Tendsto (fun n => upper (g n)) atTop (nhds c) := by
    simpa only [add_sub_cancel, add_zero] using hllim.add hdlim
  refine ⟨c, ?_, ?_, ?_⟩
  · exact le_ciSup hbdd 0
  · exact ciSup_le hbb
  · intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hllim hulim
      (fun n => lower_le (g n) i) (fun n => le_upper (g n) i)

end Transition
end FiniteResampling

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

/-- Full labelled hyperedges; allowing empty hyperedges causes no change to clusters. -/
abbrev Hypergraph (V : Type uV) (E : Type uE) := E → Set V

def Adj (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  ∃ e, ω e = true ∧ Disjoint (H e) D ∧ x ∈ H e ∧ y ∈ H e

def Connected (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x y : V) : Prop :=
  Relation.ReflTransGen (Adj H ω D) x y

def cluster (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) : Set V :=
  {y | Connected H ω D x y}

def clusters (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) : Set V :=
  {y | ∃ x ∈ S, y ∈ cluster H ω D x}

def Meets (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected H ω D x y

theorem adj_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Adj H ω D x y) : Adj H ω D y x := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd, hy, hx⟩

theorem connected_symm {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y : V}
    (h : Connected H ω D x y) : Connected H ω D y x := by
  induction h with
  | refl => exact .refl
  | tail _ hxy ih => exact ih.head (adj_symm hxy)

theorem connected_refl (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) :
    Connected H ω D x x := .refl

theorem connected_trans {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x y z : V}
    (hxy : Connected H ω D x y) (hyz : Connected H ω D y z) :
    Connected H ω D x z := hxy.trans hyz

theorem mem_cluster_self (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (x : V) :
    x ∈ cluster H ω D x := .refl

theorem adj_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') {x y : V} (h : Adj H ω D' x y) : Adj H ω D x y := by
  obtain ⟨e, he, hd, hx, hy⟩ := h
  exact ⟨e, he, hd.mono_right hDD, hx, hy⟩

theorem cluster_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' : Set V}
    (hDD : D ⊆ D') (x : V) : cluster H ω D' x ⊆ cluster H ω D x :=
  Relation.ReflTransGen.mono (fun _ _ => adj_mono_delete hDD) x

theorem clusters_mono_delete {H : Hypergraph V E} {ω : E → Bool} {D D' S : Set V}
    (hDD : D ⊆ D') : clusters H ω D' S ⊆ clusters H ω D S := by
  rintro y ⟨x, hx, hy⟩
  exact ⟨x, hx, cluster_mono_delete hDD x hy⟩

theorem clusters_contains (H : Hypergraph V E) (ω : E → Bool) (D S : Set V) :
    S ⊆ clusters H ω D S := fun x hx => ⟨x, hx, .refl⟩

theorem cluster_closed {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {s x y : V}
    (hx : x ∈ cluster H ω D s) (hxy : Adj H ω D x y) : y ∈ cluster H ω D s :=
  hx.tail hxy

theorem clusters_closed {H : Hypergraph V E} {ω : E → Bool} {D S : Set V} {x y : V}
    (hx : x ∈ clusters H ω D S) (hxy : Adj H ω D x y) : y ∈ clusters H ω D S := by
  obtain ⟨s, hs, hx⟩ := hx
  exact ⟨s, hs, hx.tail hxy⟩

theorem cluster_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D : Set V} {x : V}
    (hx : x ∉ D) : Disjoint (cluster H ω D x) D := by
  apply Set.disjoint_left.mpr
  intro y hy
  induction hy with
  | refl => exact hx
  | @tail z y _ hzy _ =>
    obtain ⟨e, _, hd, _, hy⟩ := hzy
    exact fun hyD => Set.disjoint_left.mp hd hy hyD

theorem clusters_avoids_deleted {H : Hypergraph V E} {ω : E → Bool} {D S : Set V}
    (hSD : Disjoint S D) : Disjoint (clusters H ω D S) D := by
  apply Set.disjoint_left.mpr
  rintro y ⟨x, hx, hy⟩ hyD
  exact Set.disjoint_left.mp (cluster_avoids_deleted
    (fun hxD => Set.disjoint_left.mp hSD hx hxD)) hy hyD

/-- Disjointness of a full cluster from a tested set is also disjointness from its
entire union of clusters, the fact used in the first-listed-node partition. -/
theorem cluster_disjoint_clusters_iff {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} :
    Disjoint (cluster H ω D x) (clusters H ω D S) ↔
      Disjoint (cluster H ω D x) S := by
  constructor
  · exact fun h => h.mono_right (clusters_contains H ω D S)
  · intro h
    apply Set.disjoint_left.mpr
    rintro y hy ⟨s, hs, hsy⟩
    exact Set.disjoint_left.mp h (connected_trans hy (connected_symm hsy)) hs

/-- Deleting a union of clusters does not change any of the other clusters.
This is deterministic, before any product-law conditioning. -/
theorem cluster_delete_clusters {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {x : V} (hx : x ∉ clusters H ω D S) :
    cluster H ω (D ∪ clusters H ω D S) x = cluster H ω D x := by
  apply Set.Subset.antisymm (cluster_mono_delete Set.subset_union_left x)
  intro y hy
  have hall : ∀ z ∈ cluster H ω D x, z ∉ clusters H ω D S := by
    rintro z hz ⟨s, hs, hsz⟩
    exact hx ⟨s, hs, connected_trans hsz (connected_symm hz)⟩
  induction hy with
  | refl => exact .refl
  | @tail z y hxz hzy ih =>
    apply ih.tail
    obtain ⟨e, he, hd, hz, hy⟩ := hzy
    refine ⟨e, he, Disjoint.union_right hd ?_, hz, hy⟩
    apply Set.disjoint_left.mpr
    intro a ha hbad
    exact hall z hxz (clusters_closed hbad ⟨e, he, hd, ha, hz⟩)

/-- Changing bits on hyperedges disjoint from C(S) cannot change C(S).
This is the key measurability assertion required for exact-cluster conditioning. -/
theorem clusters_eq_of_agree_incident {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V}
    (hagree : ∀ e, ¬ Disjoint (H e) (clusters H ω D S) → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  have hnew : clusters H ω' D S ⊆ clusters H ω D S := by
    rintro y ⟨x, hx, hy⟩
    have hr : ∀ z, Connected H ω' D x z → Connected H ω D x z := by
      intro z hz
      induction hz with
      | refl => exact .refl
      | @tail a b _ hab ia =>
        obtain ⟨e, he, hd, ha, hb⟩ := hab
        have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
          intro h
          exact Set.disjoint_left.mp h ha ⟨x, hx, ia⟩
        exact ia.tail ⟨e, (hagree e hi) ▸ he, hd, ha, hb⟩
    exact ⟨x, hx, hr y hy⟩
  apply Set.Subset.antisymm hnew
  rintro y ⟨x, hx, hy⟩
  have hr : ∀ z, Connected H ω D x z → Connected H ω' D x z := by
    intro z hz
    induction hz with
    | refl => exact .refl
    | @tail a b hxa hab ia =>
      obtain ⟨e, he, hd, ha, hb⟩ := hab
      have hi : ¬ Disjoint (H e) (clusters H ω D S) := by
        intro h
        exact Set.disjoint_left.mp h ha ⟨x, hx, hxa⟩
      exact ia.tail ⟨e, (hagree e hi).trans he, hd, ha, hb⟩
  exact ⟨x, hx, hr y hy⟩

def ClusterDomain (s : V) (S : Set V) : Set (Set V) :=
  {U | s ∈ U ∧ Disjoint U S}

noncomputable def residualSample (H : Hypergraph V E) (ω : E → Bool)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact if s ∈ clusters H ω U S then 0 else
    F (cluster H ω (clusters H ω U S) s) -
    F (cluster H ω (clusters H ω U S ∪ U) s)

theorem residual_cluster_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) :
    cluster H ω (clusters H ω U S) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted hs).mono_right ?_⟩
  exact clusters_contains H ω U S

theorem residual_cluster_union_mem_domain {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} (hs : s ∉ clusters H ω U S) (hsU : s ∉ U) :
    cluster H ω (clusters H ω U S ∪ U) s ∈ ClusterDomain s S := by
  refine ⟨.refl, (cluster_avoids_deleted (fun h => h.elim hs hsU)).mono_right ?_⟩
  exact (clusters_contains H ω U S).trans Set.subset_union_left

theorem residualSample_nonneg {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U : Set V} {F : Set V → ℝ} (hsU : s ∉ U)
    (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualSample H ω s S U F := by
  classical
  unfold residualSample
  split_ifs with hs
  · exact le_rfl
  · exact sub_nonneg.mpr (hF (residual_cluster_union_mem_domain hs hsU)
      (residual_cluster_mem_domain hs) (cluster_mono_delete Set.subset_union_left s))

theorem residualSample_mono {H : Hypergraph V E} {ω : E → Bool}
    {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualSample H ω s S U F ≤ residualSample H ω s S U' F := by
  classical
  have hsU : s ∉ U := fun hs => hsU' (hUU hs)
  by_cases hs : s ∈ clusters H ω U S
  · rw [residualSample, ite_eq_left hs]
    exact residualSample_nonneg hsU' hF
  · have hs' : s ∉ clusters H ω U' S :=
      fun h => hs (clusters_mono_delete hUU h)
    have hfirst : F (cluster H ω (clusters H ω U S) s) ≤
        F (cluster H ω (clusters H ω U' S) s) :=
      hF (residual_cluster_mem_domain hs) (residual_cluster_mem_domain hs')
        (cluster_mono_delete (clusters_mono_delete hUU) s)
    have heq : cluster H ω (clusters H ω U S ∪ U) s = cluster H ω U s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs
    have heq' : cluster H ω (clusters H ω U' S ∪ U') s = cluster H ω U' s := by
      rw [Set.union_comm]
      exact cluster_delete_clusters hs'
    have hsecond : F (cluster H ω (clusters H ω U' S ∪ U') s) ≤
        F (cluster H ω (clusters H ω U S ∪ U) s) := by
      apply hF (residual_cluster_union_mem_domain hs' hsU')
        (residual_cluster_union_mem_domain hs hsU)
      rw [heq, heq']
      exact cluster_mono_delete hUU s
    simp only [residualSample, ite_eq_right hs, ite_eq_right hs']
    exact sub_le_sub hfirst hsecond

/-- Bits on deleted hyperedges are irrelevant to the surviving clusters. -/
theorem cluster_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) (s : V) :
    cluster H ω' D s = cluster H ω D s := by
  have hrel : Adj H ω' D = Adj H ω D := by
    funext x y
    apply propext
    constructor <;> rintro ⟨e, he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd) ▸ he, hd, hx, hy⟩
    · exact ⟨e, (hagree e hd).trans he, hd, hx, hy⟩
  unfold cluster Connected
  rw [hrel]

theorem clusters_eq_of_agree_disjoint {H : Hypergraph V E} {ω ω' : E → Bool}
    {D S : Set V} (hagree : ∀ e, Disjoint (H e) D → ω' e = ω e) :
    clusters H ω' D S = clusters H ω D S := by
  unfold clusters
  simp only [cluster_eq_of_agree_disjoint hagree]

theorem clusters_singleton (H : Hypergraph V E) (ω : E → Bool) (D : Set V) (s : V) :
    clusters H ω D {s} = cluster H ω D s := by
  ext y
  simp [clusters]

/-- Deleting a cluster does not change the union of any disjoint clusters. -/
theorem clusters_delete_cluster {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} (h : Disjoint (cluster H ω D s) S) :
    clusters H ω (D ∪ cluster H ω D s) S = clusters H ω D S := by
  ext y
  constructor
  · exact fun hy => clusters_mono_delete Set.subset_union_left hy
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, hx, ?_⟩
    have heq := cluster_delete_clusters (H := H) (ω := ω) (D := D) (S := {s})
      (x := x) (by simpa only [clusters_singleton] using (fun hxs => Set.disjoint_left.mp h hxs hx))
    rw [clusters_singleton] at heq
    rwa [heq]

theorem cluster_eq_of_connected {H : Hypergraph V E} {ω : E → Bool} {D : Set V}
    {s t : V} (hst : Connected H ω D s t) :
    cluster H ω D s = cluster H ω D t := by
  ext y
  exact ⟨fun hy => connected_trans (connected_symm hst) hy,
    fun hy => connected_trans hst hy⟩

def earlier {n : ℕ} (x : Fin n → V) (k : Fin n) : Set V :=
  {v | ∃ j, j < k ∧ x j = v}

def firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V) (ω : E → Bool)
    (D : Set V) (k i : Fin n) : Prop :=
  Disjoint (cluster H ω D (x k)) (earlier x k) ∧ Connected H ω D (x k) (x i)

theorem firstRoot_iff {n : ℕ} {H : Hypergraph V E} {x : Fin n → V} {ω : E → Bool}
    {D : Set V} {k i : Fin n} :
    firstRoot H x ω D k i ↔ Connected H ω D (x k) (x i) ∧
      ∀ j < k, ¬Connected H ω D (x j) (x i) := by
  constructor
  · rintro ⟨hd, hc⟩
    refine ⟨hc, ?_⟩
    intro j hj hji
    exact Set.disjoint_left.mp hd (connected_trans hc (connected_symm hji)) ⟨j, hj, rfl⟩
  · rintro ⟨hc, hf⟩
    refine ⟨Set.disjoint_left.mpr ?_, hc⟩
    rintro y hy ⟨j, hj, rfl⟩
    exact hf j hj (connected_trans (connected_symm hy) hc)

theorem exists_unique_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) : ∃! k, firstRoot H x ω D k i := by
  classical
  let J := Finset.univ.filter (fun j => Connected H ω D (x j) (x i))
  have hJ : J.Nonempty := ⟨i, by simp [J, connected_refl]⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hkc : Connected H ω D (x k) (x i) := (Finset.mem_filter.mp hkJ).2
  have hf : firstRoot H x ω D k i := by
    apply firstRoot_iff.mpr
    refine ⟨hkc, ?_⟩
    intro j hj hc
    have hkj : k ≤ j := Finset.min'_le J j (by simp [J, hc])
    exact (not_le_of_gt hj) hkj
  refine ⟨k, hf, ?_⟩
  intro j hj
  apply le_antisymm
  · by_contra h
    exact (firstRoot_iff.mp hj).2 k (lt_of_not_ge h) hkc
  · exact Finset.min'_le J j (by simp [J, (firstRoot_iff.mp hj).1])

/-- The first-listed-node partition, as a pointwise identity for any cluster
functional. This is stronger than its integrated mass identity H d = 1. -/
theorem sum_firstRoot {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (D : Set V) (i : Fin n) (F : Set V → ℝ) :
    (∑ k, if firstRoot H x ω D k i then F (cluster H ω D (x k)) else 0) =
      F (cluster H ω D (x i)) := by
  classical
  obtain ⟨k, hk, huniq⟩ := exists_unique_firstRoot H x ω D i
  rw [Finset.sum_eq_single k]
  · rw [ite_eq_left hk, cluster_eq_of_connected hk.2]
  · intro j _ hj
    rw [ite_eq_right (fun h => hj (huniq j h))]
  · simp

section FiniteLaw
variable [Fintype E]

noncomputable def law (p : E → Set.Icc (0 : ℝ) 1) : Measure (E → Bool) :=
  Measure.pi (fun e => bernoulliMeasure true false (p e))

instance law_probability (p : E → Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (law p) := by
  unfold law
  infer_instance

/-- Functions of complementary finite sets of independent bits are independent.
The dependence conditions are extensional, avoiding auxiliary sigma-algebras. -/
theorem independent_of_disjoint_bits (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by
  classical
  let f' : (J → Bool) → ℝ := fun a => f (fun e => if h : e ∈ J then a ⟨e,h⟩ else false)
  let g' : (↑(Jᶜ) → Bool) → ℝ := fun a =>
    g (fun e => if h : e ∈ Jᶜ then a ⟨e,h⟩ else false)
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (law p) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have h := (hi.indepFun_finset J Jᶜ disjoint_compl_right
    (fun e => measurable_pi_apply e)).comp
    (measurable_of_countable f') (measurable_of_countable g')
  have heqf : (f' ∘ (fun (ω : E → Bool) (e : J) => ω e)) = f := by
    funext ω
    apply hf
    intro e he
    simp [he]
  have heqg : (g' ∘ (fun (ω : E → Bool) (e : ↑(Jᶜ)) => ω e)) = g := by
    funext ω
    apply hg
    intro e he
    simp [he]
  rwa [heqf, heqg] at h

/-- The exact-cluster indicator sees no bit on a hyperedge disjoint from W,
including when the cluster was sampled after an earlier deletion D. -/
theorem exact_cluster_independent (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    IndepFun (fun ω => if clusters H ω D S = W then (1 : ℝ) else 0) g (law p) := by
  classical
  apply independent_of_disjoint_bits p (Finset.univ.filter (fun e => ¬ Disjoint (H e) W))
  · intro ω ω' hagree
    have heq : clusters H ω' D S = W ↔ clusters H ω D S = W := by
      constructor
      · intro h
        have hh : clusters H ω D S = clusters H ω' D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact (hagree e (by simp [he])).symm
        exact hh.trans h
      · intro h
        have hh : clusters H ω' D S = clusters H ω D S := by
          apply clusters_eq_of_agree_incident
          intro e he
          rw [h] at he
          exact hagree e (by simp [he])
        exact hh.trans h
    simp only [heq]
  · intro ω ω' hagree
    apply hg ω ω'
    intro e he
    exact hagree e (by simp [he])

/-- Integrated exact-cluster independence, with no positivity restriction on
an exact cluster event (zero probability events also satisfy the identity). -/
theorem exact_cluster_integral (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S W : Set V) (g : (E → Bool) → ℝ)
    (hg : ∀ ω ω', (∀ e, Disjoint (H e) W → ω' e = ω e) → g ω' = g ω) :
    (∫ ω, (if clusters H ω D S = W then (1 : ℝ) else 0) * g ω ∂law p) =
      (∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p) *
        ∫ ω, g ω ∂law p := by
  classical
  exact (exact_cluster_independent H p D S W g hg).integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

/-- Partition a finite expectation by exact values, without conditional-probability
notation and without requiring positive individual atom masses. -/
theorem integral_eq_sum_fibers {I : Type uI} [Fintype I] [DecidableEq I]
    (p : E → Set.Icc (0 : ℝ) 1) (X : (E → Bool) → I) (f : (E → Bool) → ℝ) :
    (∫ ω, f ω ∂law p) = ∑ i, ∫ ω, if X ω = i then f ω else 0 ∂law p := by
  classical
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  congr 1
  funext ω
  simp

noncomputable def meanAfterDelete (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (W : Set V) (F : Set V → ℝ) : ℝ :=
  ∫ ω, F (cluster H ω W s) ∂law p

noncomputable def resample (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S : Set V) (F : Set V → ℝ) (U : Set V) : ℝ :=
  ∫ ω, meanAfterDelete H p s (clusters H ω U S) F ∂law p

noncomputable def residualMean (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (s : V) (S U : Set V) (F : Set V → ℝ) : ℝ := by
  classical
  exact ∫ ω, if s ∈ clusters H ω U S then 0 else
    meanAfterDelete H p s (clusters H ω U S) F -
      meanAfterDelete H p s (clusters H ω U S ∪ U) F ∂law p

theorem residualMean_eq_integral [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F = ∫ ω, residualSample H ω s S U F ∂law p := by
  classical
  unfold residualMean
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω U S),
    integral_eq_sum_fibers p (fun ω => clusters H ω U S)]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hs : s ∈ W
  · have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun _ => (0 : ℝ)) := by
      funext ω
      split_ifs with h <;> simp_all
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) = (fun _ => (0 : ℝ)) := by
      funext ω
      unfold residualSample
      split_ifs with h <;> simp_all
    rw [hleft, hright]
  · let g : (E → Bool) → ℝ := fun ω =>
        F (cluster H ω W s) - F (cluster H ω (W ∪ U) s)
    have hind := exact_cluster_integral H p U S W g (by
      intro ω ω' hagree
      dsimp [g]
      rw [cluster_eq_of_agree_disjoint hagree s,
        cluster_eq_of_agree_disjoint (fun e he => hagree e (he.mono_right Set.subset_union_left)) s])
    have hleft : (fun ω => if clusters H ω U S = W then
        (if s ∈ clusters H ω U S then 0 else
          meanAfterDelete H p s (clusters H ω U S) F -
          meanAfterDelete H p s (clusters H ω U S ∪ U) F) else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) *
          (∫ ω', g ω' ∂law p)) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, meanAfterDelete,
          integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      · simp [h]
    have hright : (fun ω => if clusters H ω U S = W then
        residualSample H ω s S U F else 0) =
        (fun ω => (if clusters H ω U S = W then (1 : ℝ) else 0) * g ω) := by
      funext ω
      by_cases h : clusters H ω U S = W
      · simp [h, hs, g, residualSample]
      · simp [h]
    rw [hleft, hright, integral_mul_const, hind]

theorem residualMean_nonneg [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hsU : s ∉ U) (hF : MonotoneOn F (ClusterDomain s S)) :
    0 ≤ residualMean H p s S U F := by
  rw [residualMean_eq_integral]
  exact integral_nonneg (fun _ => residualSample_nonneg hsU hF)

theorem residualMean_mono [Fintype V] {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U U' : Set V} {F : Set V → ℝ}
    (hUU : U ⊆ U') (hsU' : s ∉ U') (hF : MonotoneOn F (ClusterDomain s S)) :
    residualMean H p s S U F ≤ residualMean H p s S U' F := by
  rw [residualMean_eq_integral, residualMean_eq_integral]
  exact integral_mono (Integrable.of_finite) (Integrable.of_finite)
    (fun _ => residualSample_mono hUU hsU' hF)

theorem meanAfterDelete_antitone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S W W' : Set V} {F : Set V → ℝ}
    (hWW : W ⊆ W') (hSW : S ⊆ W) (hs : s ∉ W')
    (hF : MonotoneOn F (ClusterDomain s S)) :
    meanAfterDelete H p s W' F ≤ meanAfterDelete H p s W F := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply hF
  · exact ⟨.refl, (cluster_avoids_deleted hs).mono_right (hSW.trans hWW)⟩
  · exact ⟨.refl, (cluster_avoids_deleted (fun h => hs (hWW h))).mono_right hSW⟩
  · exact cluster_mono_delete hWW s

theorem resample_monotone {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S : Set V} {F : Set V → ℝ}
    (hF : MonotoneOn F (ClusterDomain s S)) :
    MonotoneOn (resample H p s S F) (ClusterDomain s S) := by
  intro U hU U' hU' hUU
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  apply meanAfterDelete_antitone (clusters_mono_delete hUU) (clusters_contains H ω U' S)
  · exact fun hs => Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1
  · exact hF

theorem resample_nonneg {H : Hypergraph V E}
    {p : E → Set.Icc (0 : ℝ) 1} {s : V} {S U : Set V} {F : Set V → ℝ}
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) (hU : U ∈ ClusterDomain s S) :
    0 ≤ resample H p s S F U := by
  apply integral_nonneg
  intro ω
  apply integral_nonneg
  intro ω'
  apply hF
  exact ⟨.refl, (cluster_avoids_deleted (fun hs =>
    Set.disjoint_left.mp (clusters_avoids_deleted hU.2.symm) hs hU.1)).mono_right
      (clusters_contains H ω U S)⟩

noncomputable def clusterMass (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (D S W : Set V) : ℝ :=
  ∫ ω, if clusters H ω D S = W then (1 : ℝ) else 0 ∂law p

/-- The exact-cluster conditional expectation used in the column partition. -/
theorem cluster_conditioning (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S W : Set V) (F : Set V → ℝ)
    (hs : s ∉ W) :
    (∫ ω, if clusters H ω D S = W then F (cluster H ω D s) else 0 ∂law p) =
      clusterMass H p D S W * meanAfterDelete H p s (D ∪ W) F := by
  classical
  have hind := exact_cluster_integral H p D S W
    (fun ω => F (cluster H ω (D ∪ W) s)) (by
      intro ω ω' hagree
      rw [cluster_eq_of_agree_disjoint
        (fun e he => hagree e (he.mono_right Set.subset_union_right)) s])
  unfold clusterMass meanAfterDelete
  rw [← hind]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases h : clusters H ω D S = W
  · have hcs : cluster H ω (D ∪ W) s = cluster H ω D s := by
      rw [← h]
      exact cluster_delete_clusters (by rwa [h])
    simp [h, hcs]
  · simp [h]

/-- Multiply the exact-cluster identity by an arbitrary function of the cluster.
No positive-probability conditioning is needed. -/
theorem exact_cluster_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (D S : Set V) (f : Set V → ℝ)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, f (clusters H ω D S) * g ω (clusters H ω D S) ∂law p) =
      ∫ ω, f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * g ω (clusters H ω D S) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) * g ω U)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      f (clusters H ω D S) * (∫ ω', g ω' (clusters H ω D S) ∂law p) else 0) =
      (fun ω => f U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        (∫ ω', g ω' U ∂law p))) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const,
    exact_cluster_integral H p D S U (fun ω => g ω U) (hg U)]

/-- Exact-cluster integration of a functional rooted outside the measured cluster. -/
theorem conditioning_weight [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (D S : Set V)
    (w : Set V → ℝ) (F : Set V → ℝ) (hw : ∀ U, s ∈ U → w U = 0) :
    (∫ ω, w (clusters H ω D S) * F (cluster H ω D s) ∂law p) =
      ∫ ω, w (clusters H ω D S) *
        meanAfterDelete H p s (D ∪ clusters H ω D S) F ∂law p := by
  classical
  rw [integral_eq_sum_fibers p (fun ω => clusters H ω D S),
    integral_eq_sum_fibers p (fun ω => clusters H ω D S)]
  apply Finset.sum_congr rfl
  intro U _
  have hleft : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * F (cluster H ω D s) else 0) =
      (fun ω => w U * (if clusters H ω D S = U then F (cluster H ω D s) else 0)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  have hright : (fun ω => if clusters H ω D S = U then
      w (clusters H ω D S) * meanAfterDelete H p s (D ∪ clusters H ω D S) F else 0) =
      (fun ω => w U * ((if clusters H ω D S = U then (1:ℝ) else 0) *
        meanAfterDelete H p s (D ∪ U) F)) := by
    funext ω
    by_cases h : clusters H ω D S = U <;> simp [h]
  rw [hleft, hright, integral_const_mul, integral_const_mul, integral_mul_const]
  by_cases hs : s ∈ U
  · simp [hw U hs]
  · rw [cluster_conditioning H p s D S U F hs]
    rfl

/-- For residuals, after conditioning on W the second sample may instead be
read in the original configuration on the graph with U deleted. -/
theorem residualMean_alternative [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S U : Set V) (F : Set V → ℝ) :
    residualMean H p s S U F =
      ∫ ω, if s ∈ clusters H ω U S then 0 else
        meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s) ∂law p := by
  classical
  have hc := conditioning_weight H p s U S
    (fun W => if s ∈ W then 0 else 1) F (by intro W h; simp [h])
  have heq₁ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F - F (cluster H ω U s)) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          F (cluster H ω U s)) := by
    funext ω
    split_ifs <;> simp
  have heq₂ : (fun ω => if s ∈ clusters H ω U S then (0:ℝ) else
      meanAfterDelete H p s (clusters H ω U S) F -
        meanAfterDelete H p s (clusters H ω U S ∪ U) F) =
      (fun ω => (if s ∈ clusters H ω U S then 0 else meanAfterDelete H p s
        (clusters H ω U S) F) - (if s ∈ clusters H ω U S then 0 else 1) *
          meanAfterDelete H p s (U ∪ clusters H ω U S) F) := by
    funext ω
    split_ifs <;> simp [Set.union_comm]
  unfold residualMean
  rw [heq₁, heq₂, integral_sub (Integrable.of_finite) (Integrable.of_finite),
    integral_sub (Integrable.of_finite) (Integrable.of_finite), hc]

noncomputable def column {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ)
    (i : Fin n) : ℝ := by
  classical
  exact ∫ ω, if firstRoot H x ω ∅ k i then F (cluster H ω ∅ (x k)) else 0 ∂law p

theorem sum_column {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) (i : Fin n) :
    ∑ k, column H p x k F i = ∫ ω, F (cluster H ω ∅ (x i)) ∂law p := by
  classical
  unfold column
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => sum_firstRoot H x ω ∅ i F)

/-- The first-listed-event column disintegrates over its exact root cluster. -/
theorem column_conditional_expectation [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → Set V → ℝ)
    (hg : ∀ U ω ω', (∀ e, Disjoint (H e) U → ω' e = ω e) → g ω' U = g ω U) :
    (∫ ω, if firstRoot H x ω ∅ k i then g ω (cluster H ω ∅ (x k)) else 0 ∂law p) =
      column H p x k (fun U => ∫ ω, g ω U ∂law p) i := by
  classical
  have h := exact_cluster_weight H p ∅ {x k}
    (fun U => if Disjoint U (earlier x k) ∧ x i ∈ U then 1 else 0) g hg
  simp only [clusters_singleton] at h
  have heq (q : (E → Bool) → Set V → ℝ) :
      (fun ω => if firstRoot H x ω ∅ k i then q ω (cluster H ω ∅ (x k)) else 0) =
      (fun ω => (if Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
        x i ∈ cluster H ω ∅ (x k) then (1:ℝ) else 0) * q ω (cluster H ω ∅ (x k))) := by
    funext ω
    by_cases hf : firstRoot H x ω ∅ k i
    · have hf' : Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k) := hf
      simp [hf, hf']
    · have hf' : ¬(Disjoint (cluster H ω ∅ (x k)) (earlier x k) ∧
          x i ∈ cluster H ω ∅ (x k)) := hf
      simp [hf, hf']
  rw [← heq g, ← heq (fun _ U => ∫ ω, g ω U ∂law p)] at h
  exact h

theorem column_resample [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F else 0 ∂law p := by
  classical
  have h := column_conditional_expectation H p x k i
    (fun ω U => meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F)
    (by intro U ω ω' hagree; rw [clusters_eq_of_agree_disjoint hagree])
  change _ = column H p x k (resample H p (x k) (earlier x k) F) i at h
  rw [← h]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · have heq := clusters_delete_cluster hf.1
    simp only [Set.empty_union] at heq
    simp [hf, heq]
  · simp [hf]

/-- An earlier list segment is included in every later segment. -/
theorem earlier_mono {n : ℕ} (x : Fin n → V) {k j : Fin n} (hkj : k ≤ j) :
    earlier x k ⊆ earlier x j := by
  rintro y ⟨l, hl, hly⟩
  exact ⟨l, lt_of_lt_of_le hl hkj, hly⟩

/-- The residual term after conditioning on C(x_j), retaining the original
configuration only on hyperedges disjoint from that cluster. -/
theorem column_residual [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k j i : Fin n)
    (hkj : k < j) (F : Set V → ℝ) :
    column H p x j (residualMean H p (x k) (earlier x k) · F) i =
      ∫ ω, if firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k) then
        meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F -
          F (cluster H ω ∅ (x k)) else 0 ∂law p := by
  classical
  have hfun : (fun U => residualMean H p (x k) (earlier x k) U F) =
      (fun U => ∫ ω, if x k ∈ clusters H ω U (earlier x k) then 0 else
        meanAfterDelete H p (x k) (clusters H ω U (earlier x k)) F -
          F (cluster H ω U (x k)) ∂law p) := by
    funext U
    exact residualMean_alternative H p (x k) (earlier x k) U F
  rw [hfun]
  rw [← column_conditional_expectation H p x j i _ (by
    intro U ω ω' hagree
    rw [clusters_eq_of_agree_disjoint hagree, cluster_eq_of_agree_disjoint hagree])]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ j i
  · have hdis : Disjoint (cluster H ω ∅ (x j)) (earlier x k) :=
      hf.1.mono_right (earlier_mono x hkj.le)
    have hs : x k ∉ cluster H ω ∅ (x j) := fun hs =>
      Set.disjoint_left.mp hf.1 hs ⟨k, hkj, rfl⟩
    have hW := clusters_delete_cluster hdis
    have hC := cluster_delete_clusters (H := H) (ω := ω) (D := ∅) (S := {x j})
      (x := x k) (by simpa only [clusters_singleton] using hs)
    simp only [Set.empty_union, clusters_singleton] at hW hC
    simp only [hf, ite_true, hW, hC, true_and]
    split_ifs <;> simp_all
  · simp [hf]

omit [Fintype E] in
/-- Separation from a union of full clusters is exactly avoidance by the root. -/
theorem disjoint_cluster_iff_root_notin {H : Hypergraph V E} {ω : E → Bool}
    {D S : Set V} {s : V} :
    Disjoint (cluster H ω D s) S ↔ s ∉ clusters H ω D S := by
  constructor
  · rintro hd ⟨t, ht, hts⟩
    exact Set.disjoint_left.mp hd (connected_symm hts) ht
  · intro hs
    apply Set.disjoint_left.mpr
    intro t hst ht
    exact hs ⟨t, ht, connected_symm hst⟩

omit [Fintype E] in
theorem firstRoot_notin_earlier_clusters {n : ℕ} {H : Hypergraph V E}
    {x : Fin n → V} {ω : E → Bool} {D : Set V} {j i k : Fin n}
    (hf : firstRoot H x ω D j i) (hkj : k ≤ j) :
    x i ∉ clusters H ω D (earlier x k) := by
  have hd := (cluster_disjoint_clusters_iff.mpr hf.1).mono_right
    (show clusters H ω D (earlier x k) ⊆ clusters H ω D (earlier x j) from by
      rintro y ⟨z, hz, hzy⟩
      exact ⟨z, earlier_mono x hkj hz, hzy⟩)
  exact fun hi => Set.disjoint_left.mp hd hf.2 hi

omit [Fintype E] in

theorem firstListed_partition {n : ℕ} (H : Hypergraph V E) (x : Fin n → V)
    (ω : E → Bool) (k i : Fin n) (a : ℝ) :
    (if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then a else 0) =
      (if firstRoot H x ω ∅ k i then a else 0) +
        ∑ j, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then a else 0 := by
  classical
  obtain ⟨j, hj, huniq⟩ := exists_unique_firstRoot H x ω ∅ i
  have hsum : (∑ l, if k < l ∧ firstRoot H x ω ∅ l i ∧
      x k ∉ clusters H ω ∅ (earlier x k) then a else 0) =
      if k < j ∧ x k ∉ clusters H ω ∅ (earlier x k) then a else 0 := by
    rw [Finset.sum_eq_single j]
    · simp only [hj, true_and]
    · intro l _ hlj
      have hlf : ¬firstRoot H x ω ∅ l i := fun h => hlj (huniq l h)
      simp [hlf]
    · simp
  rw [hsum]
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · have hi : x i ∈ clusters H ω ∅ (earlier x k) := ⟨x j, ⟨j, hjk,rfl⟩, hj.2⟩
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hjk) (huniq k h).symm
    simp [hi, hk, not_lt_of_gt hjk]
  · have hs := disjoint_cluster_iff_root_notin.mp hj.1
    have hi := firstRoot_notin_earlier_clusters hj le_rfl
    simp [hj, hs, hi]
  · have hi := firstRoot_notin_earlier_clusters hj hkj.le
    have hk : ¬firstRoot H x ω ∅ k i := fun h => (ne_of_lt hkj) (huniq k h)
    simp [hi, hk, hkj]

/-- Integrated form of the first-listed-node partition. -/
theorem integral_firstListed_partition {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n)
    (g : (E → Bool) → ℝ) :
    (∫ ω, if x k ∉ clusters H ω ∅ (earlier x k) ∧ x i ∉ clusters H ω ∅ (earlier x k)
      then g ω else 0 ∂law p) =
      (∫ ω, if firstRoot H x ω ∅ k i then g ω else 0 ∂law p) +
        ∑ j, ∫ ω, if k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
          then g ω else 0 ∂law p := by
  simp_rw [firstListed_partition H x _ k i]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_finsetSum _ (fun _ _ => Integrable.of_finite)]

/-- Subtraction under a finite expectation with the same event indicator. -/
theorem integral_indicator_sub (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) [DecidablePred P] (f g : (E → Bool) → ℝ) :
    (∫ ω, if P ω then f ω - g ω else 0 ∂law p) =
      (∫ ω, if P ω then f ω else 0 ∂law p) -
        ∫ ω, if P ω then g ω else 0 ∂law p := by
  have h : (fun ω => if P ω then f ω-g ω else 0) =
      (fun ω => (if P ω then f ω else 0) - (if P ω then g ω else 0)) := by
    funext ω
    by_cases h : P ω <;> simp [h]
  rw [h, integral_sub (Integrable.of_finite) (Integrable.of_finite)]

theorem column_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k i : Fin n) (F : Set V → ℝ) :
    column H p x k F i = column H p x k (resample H p (x k) (earlier x k) F) i +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i
        else 0 := by
  classical
  let c : (E → Bool) → ℝ := fun ω =>
    meanAfterDelete H p (x k) (clusters H ω ∅ (earlier x k)) F
  let f : (E → Bool) → ℝ := fun ω => F (cluster H ω ∅ (x k))
  let P : Fin n → (E → Bool) → Prop := fun j ω =>
    k < j ∧ firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
  have hcond := conditioning_weight H p (x k) ∅ (earlier x k)
    (fun U => if x k ∉ U ∧ x i ∉ U then 1 else 0) F (by intro U h; simp [h])
  simp only [ite_mul, one_mul, zero_mul, Set.empty_union] at hcond
  rw [integral_firstListed_partition H p x k i,
    integral_firstListed_partition H p x k i] at hcond
  change column H p x k F i + (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) =
    (∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p) +
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) at hcond
  have hbase : column H p x k (resample H p (x k) (earlier x k) F) i =
      ∫ ω, if firstRoot H x ω ∅ k i then c ω else 0 ∂law p :=
    column_resample H p x k i F
  have hres (j : Fin n) :
      (if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
        (∫ ω, if P j ω then c ω else 0 ∂law p) -
          ∫ ω, if P j ω then f ω else 0 ∂law p := by
    by_cases hkj : k < j
    · rw [ite_eq_left hkj, column_residual H p x k j i hkj F]
      rw [← integral_indicator_sub p (P j) c f]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : firstRoot H x ω ∅ j i ∧ x k ∉ clusters H ω ∅ (earlier x k)
      · simp [P, hkj, h, c, f]
      · simp [P, hkj, h]
    · simp [P, hkj]
  have hsum : (∑ j, if k < j then
      column H p x j (residualMean H p (x k) (earlier x k) · F) i else 0) =
      (∑ j, ∫ ω, if P j ω then c ω else 0 ∂law p) -
        (∑ j, ∫ ω, if P j ω then f ω else 0 ∂law p) := by
    simp_rw [hres]
    rw [Finset.sum_sub_distrib]
  rw [hsum, hbase]
  linarith

omit [Fintype E] in
/-- Closing every hyperedge isolates every node, in every deletion graph. -/
theorem cluster_all_closed (H : Hypergraph V E) (D : Set V) (s : V) :
    cluster H (fun _ => false) D s = {s} := by
  ext y
  constructor
  · intro hy
    change y = s
    induction hy with
    | refl => rfl
    | tail _ h _ => obtain ⟨e, he, _⟩ := h; simp at he
  · rintro rfl
    exact .refl

/-- A state of the alternating conditional cluster resampling chain. -/
noncomputable def nextState (H : Hypergraph V E) (s : V) (S : Set V)
    (U : ClusterDomain s S) (ω ω' : E → Bool) : ClusterDomain s S :=
  ⟨cluster H ω' (clusters H ω U.1 S) s,
    ⟨.refl, (cluster_avoids_deleted (fun hs =>
      Set.disjoint_left.mp (clusters_avoids_deleted U.2.2.symm) hs U.2.1)).mono_right
        (clusters_contains H ω U.1 S)⟩⟩

/-- The finite transition matrix for the actual two-stage cluster resampling. -/
noncomputable def resamplingTransition [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) :
    FiniteResampling.Transition (ClusterDomain s S) where
  weight U T := ∫ ω, ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p ∂law p
  nonneg U T := integral_nonneg (fun _ => integral_nonneg (fun _ => by split_ifs <;> norm_num))
  total U := by
    classical
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    have heq : (fun ω => ∑ T : ClusterDomain s S,
        ∫ ω', if nextState H s S U ω ω' = T then (1:ℝ) else 0 ∂law p) =
        (fun _ => (1:ℝ)) := by
      funext ω
      rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp
    rw [heq]
    simp

theorem resamplingTransition_act [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (F : Set V → ℝ)
    (U : ClusterDomain s S) :
    (resamplingTransition H p s S).act (fun T => F T.1) U =
      resample H p s S F U.1 := by
  classical
  unfold FiniteResampling.Transition.act resamplingTransition resample meanAfterDelete
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω'
  change (∑ T : ClusterDomain s S,
    (if nextState H s S U ω ω' = T then (1:ℝ) else 0) * F T.1) =
      F (nextState H s S U ω ω').1
  simp [ite_mul]

/-- Probability mass of the all-closed finite configuration. -/
theorem all_closed_mass (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).real {fun _ => false} = ∏ e, (1 - (p e : ℝ)) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {false} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton false)]
  simp [unitInterval.coe_symm_eq]

theorem all_closed_mass_pos (p : E → Set.Icc (0 : ℝ) 1)
    (hp : ∀ e, (p e : ℝ) < 1) : 0 < (law p).real {fun _ => false} := by
  rw [all_closed_mass]
  exact Finset.prod_pos (fun e _ => sub_pos.mpr (hp e))

/-- A uniform positive atom, without discarding any zero-mass cluster states. -/
theorem resamplingTransition_atom [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (s : V) (S : Set V) (hs : s ∉ S)
    (U : ClusterDomain s S) :
    (law p).real {fun _ => false} ≤ (resamplingTransition H p s S).weight U
      ⟨{s}, ⟨by simp, by simpa using hs⟩⟩ := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  have hi : (∫ ω' : E → Bool, if ω' = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  have hj (ω : E → Bool) : (law p).real {fun _ => false} ≤
      ∫ ω', if nextState H s S U ω ω' = z then (1:ℝ) else 0 ∂law p := by
    rw [← hi]
    apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
    intro ω'
    by_cases hc : ω' = (fun _ => false)
    · subst ω'
      have heq : nextState H s S U ω (fun _ => false) = z := by
        apply Subtype.ext
        exact cluster_all_closed H _ s
      simp [heq]
    · simp only [hc, ite_false]
      split_ifs <;> norm_num
  have h := integral_mono (μ := law p) (Integrable.of_finite) (Integrable.of_finite) hj
  simpa [resamplingTransition, z] using h

/-- The actual conditional cluster-resampling iterates tend to a nonnegative
constant. This version does not need stationarity or positive mass at every state. -/
theorem resample_tendsto_constant [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (s : V) (S : Set V) (hs : s ∉ S) (F : Set V → ℝ)
    (hF : ∀ U ∈ ClusterDomain s S, 0 ≤ F U) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ U ∈ ClusterDomain s S,
      Tendsto (fun n : ℕ => ((resample H p s S)^[n] F) U) atTop (nhds c) := by
  classical
  let z : ClusterDomain s S := ⟨{s}, ⟨by simp, by simpa using hs⟩⟩
  let : Nonempty (ClusterDomain s S) := ⟨z⟩
  let K := resamplingTransition H p s S
  let a := (law p).real {fun _ => false}
  have ha0 : 0 < a := all_closed_mass_pos p hp
  have ha1 : a ≤ 1 := measureReal_le_one
  have hatom : ∀ U, a ≤ K.weight U z := fun U => resamplingTransition_atom H p s S hs U
  obtain ⟨c, hcl, _, hlim⟩ := K.iterates_tendsto_constant z a ha0 ha1 hatom (fun U => F U.1)
  have hc : 0 ≤ c := (FiniteResampling.le_lower (fun U : ClusterDomain s S => hF U.1 U.2)).trans hcl
  have heq (n : ℕ) : (fun U : ClusterDomain s S => ((resample H p s S)^[n] F) U.1) =
      (K.act)^[n] (fun U => F U.1) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      funext U
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [← resamplingTransition_act H p s S ((resample H p s S)^[n] F) U]
      exact congrFun (congrArg K.act ih) U
  refine ⟨c, hc, ?_⟩
  intro U hU
  have h := hlim ⟨U, hU⟩
  simpa only [← heq] using h

/-- Pointwise convergence exchanges with any expectation on a finite bit space. -/
theorem tendsto_integral_finite (p : E → Set.Icc (0 : ℝ) 1)
    (f : ℕ → (E → Bool) → ℝ) (g : (E → Bool) → ℝ)
    (h : ∀ ω, Tendsto (fun n => f n ω) atTop (nhds (g ω))) :
    Tendsto (fun n => ∫ ω, f n ω ∂law p) atTop (nhds (∫ ω, g ω ∂law p)) := by
  simp_rw [integral_fintype (Integrable.of_finite)]
  exact tendsto_finsetSum _ (fun ω _ => tendsto_const_nhds.smul (h ω))

/-- Column convergence only needs convergence on its specified cluster domain. -/
theorem column_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => column H p x k (F t) i) atTop
      (nhds (column H p x k (fun _ => c) i)) := by
  unfold column
  apply tendsto_integral_finite
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i
  · simp only [hf, ite_true]
    exact h _ ⟨.refl, hf.1⟩
  · simp only [hf, ite_false]
    exact tendsto_const_nhds

/-- Unnormalized cluster columns d_k h_k. -/
noncomputable def baseMatrix {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => column H p x k (fun _ => 1) i

omit [Fintype E] in
theorem root_notin_earlier {n : ℕ} {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

theorem baseMatrix_lowerTriangular {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) : (baseMatrix H p x).IsLowerTriangular := by
  intro i j hij
  have hf (ω : E → Bool) : ¬firstRoot H x ω ∅ j i := by
    intro hf
    exact Set.disjoint_left.mp hf.1 hf.2 ⟨i, hij, rfl⟩
  simp [baseMatrix, column, hf]

/-- The diagonal mass is positive because fully closing the graph ensures E_k. -/
theorem baseMatrix_diag_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < baseMatrix H p x k k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold baseMatrix column
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : firstRoot H x (fun _ => false) ∅ k k := by
      refine ⟨?_, .refl⟩
      rw [cluster_all_closed]
      simpa using root_notin_earlier hx k
    simp [hf]
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

theorem baseMatrix_det_ne_zero {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x).det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular _ (baseMatrix_lowerTriangular H p x)]
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => ne_of_gt (baseMatrix_diag_pos H p hp x hx k))

/-- Coordinates in the basis of unnormalized cluster columns. -/
noncomputable def coeff {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (baseMatrix H p x)⁻¹ *ᵥ column H p x k F

theorem column_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (c : ℝ) :
    column H p x k (fun _ => c) = c • column H p x k (fun _ => 1) := by
  funext i
  unfold column
  change (∫ ω, if firstRoot H x ω ∅ k i then c else 0 ∂law p) =
    c * ∫ ω, if firstRoot H x ω ∅ k i then 1 else 0 ∂law p
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hf : firstRoot H x ω ∅ k i <;> simp [hf]

theorem coeff_const {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k i : Fin n) (c : ℝ) :
    coeff H p x k (fun _ => c) i = if i = k then c else 0 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have hinv : coeff H p x k (fun _ => 1) i = if i = k then 1 else 0 := by
    change ((baseMatrix H p x)⁻¹ * baseMatrix H p x) i k = _
    rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
  unfold coeff
  rw [column_const, Matrix.mulVec_smul]
  change c * coeff H p x k (fun _ => 1) i = _
  rw [hinv]
  split_ifs <;> simp

/-- Inverse-basis coordinates obey the same column identity. -/
theorem coeff_identity [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    coeff H p x k F = coeff H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then coeff H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
  have hc : column H p x k F = column H p x k (resample H p (x k) (earlier x k) F) +
      ∑ j, if k < j then column H p x j (residualMean H p (x k) (earlier x k) · F) else 0 := by
    funext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      column_identity H p x k i F
  unfold coeff
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : k < j <;> simp [h]

/-- Convergence passes to inverse-basis coordinates by finite linearity. -/
theorem coeff_tendsto {n : ℕ} (H : Hypergraph V E) (p : E → Set.Icc (0 : ℝ) 1)
    (x : Fin n → V) (k i : Fin n) (F : ℕ → Set V → ℝ) (c : ℝ)
    (h : ∀ U ∈ ClusterDomain (x k) (earlier x k),
      Tendsto (fun t => F t U) atTop (nhds c)) :
    Tendsto (fun t => coeff H p x k (F t) i) atTop
      (nhds (coeff H p x k (fun _ => c) i)) := by
  unfold coeff Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun j _ => tendsto_const_nhds.mul (column_tendsto H p x k j F c h))

theorem coeff_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (F : Set V → ℝ)
    (hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U)
    (hFm : MonotoneOn F (ClusterDomain (x k) (earlier x k))) (i : Fin n) :
    0 ≤ coeff H p x k F i := by
  suffices aux : ∀ m : ℕ, ∀ k : Fin n, n - k.val = m → ∀ F : Set V → ℝ,
      (∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ F U) →
      MonotoneOn F (ClusterDomain (x k) (earlier x k)) →
      ∀ i, 0 ≤ coeff H p x k F i by
    exact aux (n - k.val) k rfl F hF0 hFm i
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro k hkm F hF0 hFm i
    let G : ℕ → Set V → ℝ := fun t => (resample H p (x k) (earlier x k))^[t] F
    have hG0 (t : ℕ) : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ G t U := by
      induction t with
      | zero => exact hF0
      | succ t ht =>
        intro U hU
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_nonneg (H := H) (p := p) ht hU)
    have hGm (t : ℕ) : MonotoneOn (G t) (ClusterDomain (x k) (earlier x k)) := by
      induction t with
      | zero => exact hFm
      | succ t ht =>
        simpa only [G, Function.iterate_succ_apply'] using
          (resample_monotone (H := H) (p := p) ht)
    have hstep (t : ℕ) : coeff H p x k (G (t + 1)) i ≤ coeff H p x k (G t) i := by
      have hid := congrFun (coeff_identity H p x k (G t)) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hid
      have hr : 0 ≤ ∑ j : Fin n, if k < j then
          coeff H p x j (residualMean H p (x k) (earlier x k) · (G t)) i else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs with hkj
        · have hmj : n - j.val < m := by
            have hjn := j.isLt
            have hkn := k.isLt
            have hkjv : k.val < j.val := hkj
            omega
          apply ih (n - j.val) hmj j rfl _
          · intro U hU
            apply residualMean_nonneg _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU.2 hu ⟨k, hkj, rfl⟩
          · intro U hU U' hU' hUU
            apply residualMean_mono hUU _ (hGm t)
            intro hu
            exact Set.disjoint_left.mp hU'.2 hu ⟨k, hkj, rfl⟩
        · exact le_rfl
      have heq : G (t + 1) = resample H p (x k) (earlier x k) (G t) :=
        Function.iterate_succ_apply' _ _ _
      rw [heq]
      linarith
    have hant : Antitone (fun t => coeff H p x k (G t) i) :=
      antitone_nat_of_succ_le hstep
    obtain ⟨c, hc, hlim⟩ := resample_tendsto_constant H p hp (x k) (earlier x k)
      (root_notin_earlier hx k) F hF0
    have hl := coeff_tendsto H p x k i G c hlim
    have hle : coeff H p x k (fun _ => c) i ≤ coeff H p x k F i := by
      apply le_of_tendsto hl
      exact Filter.Eventually.of_forall (fun t => hant (Nat.zero_le t))
    apply le_trans _ hle
    rw [coeff_const H p hp x hx]
    split_ifs <;> positivity

/-- The observable that a cluster contains another listed vertex. -/
noncomputable def hitsOther {n : ℕ} (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0

noncomputable def isolatedMass {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) : ℝ :=
  ∫ ω, if ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) then 1 else 0 ∂law p

omit [Fintype E] in
theorem isolated_firstRoot {n : ℕ} {H : Hypergraph V E} {x : Fin n → V}
    {k : Fin n} {ω : E → Bool}
    (h : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j)) : firstRoot H x ω ∅ k k := by
  refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
  rintro y hy ⟨j, hj, rfl⟩
  exact h j (ne_of_lt hj) hy

theorem isolatedMass_pos {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < isolatedMass H p x k := by
  have hi : (∫ ω : E → Bool, if ω = (fun _ => false) then (1:ℝ) else 0 ∂law p) =
      (law p).real {fun _ => false} := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := law p) (s := {fun _ => false}) (measurableSet_singleton _))
  apply (all_closed_mass_pos p hp).trans_le
  rw [← hi]
  unfold isolatedMass
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hc : ω = (fun _ => false)
  · subst ω
    have hf : ∀ j, j ≠ k → ¬Connected H (fun _ => false) ∅ (x k) (x j) := by
      intro j hj hc
      have : x j ∈ cluster H (fun _ => false) ∅ (x k) := hc
      rw [cluster_all_closed] at this
      exact hj (hx this)
    dsimp only
    rw [ite_eq_left hf]
    simp
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

theorem column_hitsOther {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (k : Fin n) :
    column H p x k (hitsOther x k) = column H p x k (fun _ => 1) -
      Pi.single k (isolatedMass H p x k) := by
  classical
  funext i
  change column H p x k (hitsOther x k) i = column H p x k (fun _ => 1) i - _
  by_cases hik : i = k
  · subst i
    simp only [Pi.single_eq_same]
    unfold column isolatedMass
    rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases ho : ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k)
    · have hn : ¬∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        obtain ⟨j, hj, hc⟩ := ho
        exact fun h => h j hj hc
      simp [hitsOther, ho, hn]
    · have hy : ∀ j, j ≠ k → ¬Connected H ω ∅ (x k) (x j) := by
        intro j hj hc
        exact ho ⟨j, hj, hc⟩
      simp only [hitsOther, ite_eq_right ho, ite_eq_left hy, ite_eq_left (isolated_firstRoot hy)]
      norm_num
  · simp only [Pi.single_eq_of_ne hik, sub_zero]
    unfold column
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hf : firstRoot H x ω ∅ k i
    · simp [hf, hitsOther, show ∃ j, j ≠ k ∧ x j ∈ cluster H ω ∅ (x k) from ⟨i, hik, hf.2⟩]
    · simp [hf]

/-- The inverse cluster matrix has nonpositive off-diagonal entries. -/
theorem inverse_offdiag_nonpos [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) {k i : Fin n} (hik : i ≠ k) :
    (baseMatrix H p x)⁻¹ i k ≤ 0 := by
  have hF0 : ∀ U ∈ ClusterDomain (x k) (earlier x k), 0 ≤ hitsOther x k U := by
    intro U _
    unfold hitsOther
    split_ifs <;> norm_num
  have hFm : MonotoneOn (hitsOther x k) (ClusterDomain (x k) (earlier x k)) := by
    intro U _ U' _ hUU
    unfold hitsOther
    split_ifs with h h'
    · rfl
    · obtain ⟨j, hj, hc⟩ := h
      exact (h' ⟨j, hj, hUU hc⟩).elim
    · norm_num
    · rfl
  have hc := coeff_nonneg H p hp x hx k (hitsOther x k) hF0 hFm i
  have heq : coeff H p x k (hitsOther x k) i =
      -(baseMatrix H p x)⁻¹ i k * isolatedMass H p x k := by
    unfold coeff
    rw [column_hitsOther, Matrix.mulVec_sub]
    change coeff H p x k (fun _ => 1) i - _ = _
    rw [coeff_const H p hp x hx, ite_eq_right hik]
    rw [Matrix.mulVec_single]
    simp
  rw [heq] at hc
  have ha := isolatedMass_pos H p hp x hx k
  nlinarith

/-- The first-listed cluster columns partition every row. -/
theorem baseMatrix_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) :
    baseMatrix H p x *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  unfold Matrix.mulVec dotProduct baseMatrix column
  simp only [mul_one]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hs (ω : E → Bool) := sum_firstRoot H x ω ∅ i (fun _ => (1:ℝ))
  simp_rw [hs]
  simp

/-- Consequently each row of the inverse also sums to one. -/
theorem inverse_mulVec_one {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  calc
    _ = (baseMatrix H p x)⁻¹ *ᵥ (baseMatrix H p x *ᵥ (fun _ => 1)) :=
      congrArg (fun v => (baseMatrix H p x)⁻¹ *ᵥ v) (baseMatrix_mulVec_one H p x).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- Expectation vector of a cluster observable at the listed vertices. -/
noncomputable def expectationVector {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) : Fin n → ℝ :=
  fun i => ∫ ω, F (cluster H ω ∅ (x i)) ∂law p

theorem expectationVector_eq_sum_columns {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (F : Set V → ℝ) :
    expectationVector H p x F = ∑ k, column H p x k F := by
  funext i
  simp only [Finset.sum_apply, column]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [sum_firstRoot]
  rfl

/-- Increasing observables give nonnegative inverse expectation vectors. -/
theorem inverse_expectation_nonneg [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin n → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (i : Fin n) :
    0 ≤ ((baseMatrix H p x)⁻¹ *ᵥ expectationVector H p x F) i := by
  rw [expectationVector_eq_sum_columns, Matrix.mulVec_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => coeff_nonneg H p hp x hx k F
    (fun U _ => hF0 U) (hFm.monotoneOn _) i)

/-- The final diagonal entry of the inverse is reciprocal to the probability
of avoiding all preceding listed vertices. -/
theorem inverse_last_diag_mul {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) :
    (baseMatrix H p x)⁻¹ (Fin.last n) (Fin.last n) *
      baseMatrix H p x (Fin.last n) (Fin.last n) = 1 := by
  have hdet : IsUnit (baseMatrix H p x).det := isUnit_iff_ne_zero.mpr
    (baseMatrix_det_ne_zero H p hp x hx)
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (baseMatrix H p x) hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single (Fin.last n)] at h
  · exact h
  · intro j _ hj
    have hjl : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hj
    exact mul_eq_zero_of_right _ (baseMatrix_lowerTriangular H p x hjl)
  · simp

/-- Scalar consequence of the cone: a target observable large at every earlier
listed vertex must have a correspondingly large expectation at the last one. -/
theorem expectation_comparison [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n + 1) → V) (hx : Function.Injective x) (F : Set V → ℝ)
    (hF0 : ∀ U, 0 ≤ F U) (hFm : Monotone F) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ expectationVector H p x F j) :
    b * (1 - baseMatrix H p x (Fin.last n) (Fin.last n)) ≤
      expectationVector H p x F (Fin.last n) := by
  classical
  let l := Fin.last n
  let M := baseMatrix H p x
  let y := expectationVector H p x F
  have hrow : (∑ j, M⁻¹ l j) = 1 := by
    have h := congrFun (inverse_mulVec_one H p hp x hx) l
    simpa [Matrix.mulVec, dotProduct, M] using h
  have hpos : 0 ≤ ∑ j, M⁻¹ l j * y j :=
    inverse_expectation_nonneg H p hp x hx F hF0 hFm l
  have hdiff : (∑ j, M⁻¹ l j * (y j - b)) ≤ M⁻¹ l l * (y l - b) := by
    calc
      _ ≤ ∑ j, if j = l then M⁻¹ l l * (y l - b) else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = l
        · subst j; simp
        · rw [ite_eq_right hj]
          exact mul_nonpos_of_nonpos_of_nonneg
            (inverse_offdiag_nonpos H p hp x hx (Ne.symm hj)) (sub_nonneg.mpr (hb j hj))
      _ = _ := by simp
  simp_rw [mul_sub] at hdiff
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul] at hdiff
  have hlow : -b ≤ M⁻¹ l l * (y l - b) := by linarith
  have hd : 0 < M l l := baseMatrix_diag_pos H p hp x hx l
  have hprod : M⁻¹ l l * M l l = 1 := inverse_last_diag_mul H p hp x hx
  have hh := mul_le_mul_of_nonneg_right hlow hd.le
  have heq : M⁻¹ l l * (y l - b) * M l l = y l - b := by
    calc
      _ = (M⁻¹ l l * M l l) * (y l - b) := by ring
      _ = y l - b := by rw [hprod, one_mul]
  rw [heq] at hh
  change b * (1 - M l l) ≤ y l
  linarith

/-- Real probability of any event in the finite bit space. -/
noncomputable def eventProb (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) : ℝ :=
  ∫ ω, if P ω then 1 else 0 ∂law p

theorem eventProb_eq_real (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P = (law p).real {ω | P ω} := by
  simpa [eventProb, Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

theorem eventProb_compl (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p (fun ω => ¬P ω) = 1 - eventProb p P := by
  unfold eventProb
  calc
    _ = ∫ ω, (1:ℝ) - if P ω then 1 else 0 ∂law p := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro ω
      by_cases h : P ω <;> simp [h]
    _ = _ := by
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite)]
      simp

/-- Joint cluster-hit observable, preserving both target sets. -/
noncomputable def jointObservable (A T U : Set V) : ℝ :=
  if (∃ a ∈ A, a ∈ U) ∧ (∃ t ∈ T, t ∈ U) then 1 else 0

omit [Fintype E] in
theorem jointObservable_nonneg (A T U : Set V) : 0 ≤ jointObservable A T U := by
  unfold jointObservable
  split_ifs <;> norm_num

omit [Fintype E] in
theorem jointObservable_monotone (A T : Set V) : Monotone (jointObservable A T) := by
  intro U U' hUU
  unfold jointObservable
  split_ifs with h h'
  · rfl
  · obtain ⟨⟨a, ha, hau⟩, ⟨t, ht, htu⟩⟩ := h
    exact (h' ⟨⟨a, ha, hUU hau⟩, ⟨t, ht, hUU htu⟩⟩).elim
  · norm_num
  · rfl

theorem expectation_jointObservable {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) A ∧ Meets H ω ∅ (x i) T) := by
  unfold expectationVector eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  unfold jointObservable Meets cluster
  split_ifs <;> first | rfl | simp_all

theorem expectation_jointObservable_of_mem {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin n → V) (A T : Set V) (i : Fin n) (hi : x i ∈ A) :
    expectationVector H p x (jointObservable A T) i =
      eventProb p (fun ω => Meets H ω ∅ (x i) T) := by
  rw [expectation_jointObservable]
  unfold eventProb
  have ha (ω : E → Bool) : Meets H ω ∅ (x i) A := ⟨x i, hi, .refl⟩
  simp only [ha, true_and]

theorem last_diagonal_avoidance {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (x : Fin (n+1) → V) :
    baseMatrix H p x (Fin.last n) (Fin.last n) =
      1 - eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) := by
  rw [← eventProb_compl]
  unfold baseMatrix column eventProb
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hf : firstRoot H x ω ∅ (Fin.last n) (Fin.last n) ↔
      ¬Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) := by
    constructor
    · rintro ⟨hd, _⟩ ⟨a, ha, hc⟩
      exact Set.disjoint_left.mp hd hc ha
    · intro h
      refine ⟨Set.disjoint_left.mpr ?_, .refl⟩
      intro a hc ha
      exact h ⟨a, ha, hc⟩
  by_cases h : Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))
  · simp only [hf, h, not_true_eq_false, ite_false]
  · simp only [hf, h, not_false_eq_true, ite_true]

theorem joint_comparison_list [Fintype V] {n : ℕ} (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (x : Fin (n+1) → V) (hx : Function.Injective x) (T : Set V) (b : ℝ)
    (hb : ∀ j ≠ Fin.last n, b ≤ eventProb p (fun ω => Meets H ω ∅ (x j) T)) :
    b * eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n))) ≤
      eventProb p (fun ω => Meets H ω ∅ (x (Fin.last n)) (earlier x (Fin.last n)) ∧
        Meets H ω ∅ (x (Fin.last n)) T) := by
  have h := expectation_comparison H p hp x hx
    (jointObservable (earlier x (Fin.last n)) T)
    (jointObservable_nonneg _ _) (jointObservable_monotone _ _) b (by
      intro j hj
      have hm : x j ∈ earlier x (Fin.last n) :=
        ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩
      rw [expectation_jointObservable_of_mem H p x (earlier x (Fin.last n)) T j hm]
      exact hb j hj)
  rw [last_diagonal_avoidance] at h
  simpa only [sub_sub_cancel, expectation_jointObservable] using h

omit [Fintype E] in

theorem exists_target_list [Fintype V] (A : Set V) (o : V) (ho : o ∉ A) :
    ∃ n : ℕ, ∃ x : Fin (n+1) → V, Function.Injective x ∧
      x (Fin.last n) = o ∧ earlier x (Fin.last n) = A := by
  classical
  let n := Fintype.card A
  let e : Fin n ≃ A := (Fintype.equivFin A).symm
  let x : Fin (n+1) → V := Fin.snoc (fun i => (e i).1) o
  refine ⟨n, x, ?_, by simp [x], ?_⟩
  · intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact fun _ => rfl
      | cast j =>
        intro h
        have heq : o = (e j).1 := by simpa [x] using h
        exact (ho (heq ▸ (e j).2)).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        intro h
        have heq : (e i).1 = o := by simpa [x] using h
        exact (ho (heq ▸ (e i).2)).elim
      | cast j =>
        intro h
        have heq : (e i).1 = (e j).1 := by simpa [x] using h
        exact congrArg Fin.castSucc (e.injective (Subtype.ext heq))
  · ext a
    constructor
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hj.ne
      simp [x, (e i).2]
    · intro ha
      let i := e.symm ⟨a, ha⟩
      refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
      simp [x, i]

/-- The joint connection inequality for arbitrary finite targets, first for
strictly subunit hyperedge probabilities. -/
theorem joint_comparison_of_lt_one [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (hp : ∀ e, (p e : ℝ) < 1)
    (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  by_cases ho : o ∈ A
  · have ha (ω : E → Bool) : Meets H ω ∅ o A := ⟨o, ho, .refl⟩
    have h := hb o ho
    simpa [eventProb, ha] using h
  · obtain ⟨n, x, hx, hxo, hxA⟩ := exists_target_list A o ho
    have h := joint_comparison_list H p hp x hx T b (by
      intro j hj
      apply hb
      rw [← hxA]
      exact ⟨j, Fin.lt_last_iff_ne_last.mpr hj, rfl⟩)
    simpa only [hxo, hxA] using h

/-- Polynomial weight of a specified finite configuration. -/
theorem law_mass (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (law p).real {ω} = ∏ e, if ω e = true then (p e : ℝ) else 1 - (p e : ℝ) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ω e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases he : ω e <;> simp [unitInterval.coe_symm_eq]

/-- All finite event probabilities are continuous in all parameters, including
at configurations with deterministic bits. -/
theorem eventProb_tendsto (p : E → Set.Icc (0 : ℝ) 1)
    (q : ℕ → E → Set.Icc (0 : ℝ) 1)
    (hq : ∀ e, Tendsto (fun n => (q n e : ℝ)) atTop (nhds (p e : ℝ)))
    (P : (E → Bool) → Prop) :
    Tendsto (fun n => eventProb (q n) P) atTop (nhds (eventProb p P)) := by
  simp_rw [eventProb, integral_fintype (Integrable.of_finite), law_mass]
  apply tendsto_finsetSum
  intro ω _
  apply Filter.Tendsto.smul _ tendsto_const_nhds
  apply tendsto_finsetProd
  intro e _
  by_cases he : ω e = true
  · simpa [he] using hq e
  · simpa [he] using tendsto_const_nhds.sub (hq e)

/-- Strictly subunit parameters approaching arbitrary permitted parameters. -/
noncomputable def thinParameter (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨((n : ℝ) / ((n : ℝ) + 1)) * (p e : ℝ), by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
    have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    exact ⟨mul_nonneg hr0 (p e).2.1,
      (mul_le_of_le_one_right hr0 (p e).2.2).trans hr1.le⟩⟩

omit [Fintype E] in
theorem thinParameter_lt_one (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    (thinParameter p n e : ℝ) < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_of_le_one_right hr0 (p e).2.2).trans_lt hr1

omit [Fintype E] in
theorem thinParameter_tendsto (p : E → Set.Icc (0 : ℝ) 1) (e : E) :
    Tendsto (fun n => (thinParameter p n e : ℝ)) atTop (nhds (p e : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop 1
  simpa only [thinParameter, one_mul] using h.mul_const (p e : ℝ)

theorem joint_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  let q := thinParameter p
  let d : ℕ → ℝ := fun n => ∑ a : V,
    |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)|
  have hd : Tendsto d atTop (nhds 0) := by
    have h : Tendsto d atTop (nhds (∑ _a : V, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro a _
      simpa only [sub_self, abs_zero] using
        ((eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ a T)).sub
          (tendsto_const_nhds (x := eventProb p (fun ω => Meets H ω ∅ a T)))).abs
    simpa using h
  have hbound (n : ℕ) (a : V) :
      eventProb p (fun ω => Meets H ω ∅ a T) - eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤ d n := by
    apply le_trans (show eventProb p (fun ω => Meets H ω ∅ a T) -
      eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤
      |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| by
        simpa only [neg_sub] using neg_le_abs
          (eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)))
    change |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| ≤
      ∑ j : V, |eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)|
    exact Finset.single_le_sum (fun j _ => abs_nonneg
      (eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)))
      (Finset.mem_univ a)
  have hi (n : ℕ) := joint_comparison_of_lt_one H (q n) (thinParameter_lt_one p n)
    o A T (b - d n) (by intro a ha; linarith [hb a ha, hbound n a])
  have hl := ((tendsto_const_nhds (x := b)).sub hd).mul
    (eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ o A))
  have hr := eventProb_tendsto p q (thinParameter_tendsto p)
    (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T)
  have h := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hi)
  simpa only [sub_zero] using h

theorem eventProb_nonneg (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    0 ≤ eventProb p P := by
  rw [eventProb_eq_real]
  exact measureReal_nonneg

theorem eventProb_le_one (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P ≤ 1 := by
  rw [eventProb_eq_real]
  exact measureReal_le_one

theorem eventProb_mono (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop)
    (h : ∀ ω, P ω → Q ω) : eventProb p P ≤ eventProb p Q := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num

theorem eventProb_failure (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop) :
    eventProb p (fun ω => P ω ∧ ¬Q ω) = eventProb p P - eventProb p (fun ω => P ω ∧ Q ω) := by
  unfold eventProb
  rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

/-- The strengthened hyperedge failure estimate, including all fixed-bit laws. -/
theorem failure_comparison_mul [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤
      b * eventProb p (fun ω => Meets H ω ∅ o A) := by
  rw [eventProb_failure]
  have h := joint_comparison H p o A T (1-b) hb
  nlinarith

theorem failure_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤ b := by
  apply (failure_comparison_mul H p o A T b hb).trans
  exact mul_le_of_le_one_right hb0 (eventProb_le_one p _)

theorem joint_comparison_ennreal [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ≥0∞)
    (hA : A.Nonempty) (hb : ∀ a ∈ A, b ≤ law p {ω | Meets H ω ∅ a T}) :
    law p {ω | Meets H ω ∅ o A} * b ≤
      law p {ω | Meets H ω ∅ o A ∧ Meets H ω ∅ o T} := by
  have hbn : b ≠ ⊤ := by
    obtain ⟨a, ha⟩ := hA
    exact ne_top_of_le_ne_top (measure_ne_top (law p) _) (hb a ha)
  have hr := joint_comparison H p o A T b.toReal (by
    intro a ha
    rw [eventProb_eq_real, Measure.real_def]
    exact ENNReal.toReal_mono (measure_ne_top (law p) _) (hb a ha))
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (measure_ne_top (law p) _) hbn)
    (measure_ne_top (law p) _)).mp
  simpa only [ENNReal.toReal_mul, eventProb_eq_real, Measure.real_def, mul_comm] using hr

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

/-- The connector presentation uses two directed copies of each undirected
edge; duplication does not change any reachable starred vertex. Nonedges are
isolated connector nodes. -/
abbrev Node (V : Type uV) := V ⊕ (V × V)

def stars : Hypergraph (Node V) V := fun x z =>
  match z with
  | Sum.inl y => y = x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (e.1 = x ∨ e.2 = x)

def OpenAdj (ω : V → Bool) (x y : V) : Prop :=
  G.Adj x y ∧ ω x = true ∧ ω y = true

def Connected (ω : V → Bool) (x y : V) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (OpenAdj G ω) x y

def Meets (ω : V → Bool) (x : V) (T : Set V) : Prop :=
  ∃ y ∈ T, Connected G ω x y

theorem connected_refl {ω : V → Bool} {x : V} (hx : ω x = true) :
    Connected G ω x x := ⟨hx, .refl⟩

theorem connected_open_right {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) : ω y = true := by
  obtain ⟨hx, h⟩ := h
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact hab.2.2

theorem connected_extend {ω : V → Bool} {o x y : V}
    (h : Connected G ω o x) (hxy : G.Adj x y) (hy : ω y = true) :
    Connected G ω o y :=
  ⟨h.1, h.2.tail ⟨hxy, connected_open_right G h, hy⟩⟩

theorem connected_to_stars {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) :
    HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y) := by
  obtain ⟨_, h⟩ := h
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    apply ih.trans
    apply Relation.ReflTransGen.trans (b := Sum.inr (a,b))
    · exact Relation.ReflTransGen.single
        ⟨a, hab.2.1, Set.disjoint_empty _, rfl, hab.1, Or.inl rfl⟩
    · exact Relation.ReflTransGen.single
        ⟨b, hab.2.2, Set.disjoint_empty _, ⟨hab.1, Or.inr rfl⟩, rfl⟩

/-- Predicate propagated along a hyperedge path. It explicitly retains the
site-open condition, including in the zero-edge case. -/
def Supported (ω : V → Bool) (o : V) : Node V → Prop
  | Sum.inl x => Connected G ω o x
  | Sum.inr e => G.Adj e.1 e.2 ∧ (Connected G ω o e.1 ∨ Connected G ω o e.2)

theorem supported_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Supported G ω o z) (hz : z ∈ stars G x) (hx : ω x = true) :
    Connected G ω o x := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    obtain ⟨_, hc | hc⟩ := h
    · rcases hm with rfl | rfl
      · exact hc
      · exact connected_extend G hc huv hx
    · rcases hm with rfl | rfl
      · exact connected_extend G hc huv.symm hx
      · exact hc

theorem supported_of_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Connected G ω o x) (hz : z ∈ stars G x) : Supported G ω o z := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    refine ⟨huv, ?_⟩
    rcases hm with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

theorem connected_of_stars {ω : V → Bool} {x y : V} (hx : ω x = true)
    (h : HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y)) :
    Connected G ω x y := by
  have hp : ∀ {z z' : Node V}, Supported G ω x z →
      HyperedgeComparison.Connected (stars G) ω ∅ z z' → Supported G ω x z' := by
    intro z z' hs hh
    induction hh with
    | refl => exact hs
    | @tail a b _ hab ih =>
      obtain ⟨e,he,_,ha,hb⟩ := hab
      exact supported_of_label G (supported_label G ih ha he) hb
  exact hp (z := Sum.inl x) (z' := Sum.inl y) (connected_refl G hx) h

theorem meets_to_stars {ω : V → Bool} {o : V} {T : Set V}
    (h : Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨Sum.inl t, ⟨t,ht,rfl⟩, connected_to_stars G hc⟩

theorem meets_of_stars {ω : V → Bool} {o : V} {T : Set V} (ho : ω o = true)
    (h : HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T)) :
    Meets G ω o T := by
  obtain ⟨_,⟨t,ht,rfl⟩,hc⟩ := h
  exact ⟨t,ht,connected_of_stars G ho hc⟩

theorem failure_subset_hyperedge {ω : V → Bool} {o : V} {A T : Set V}
    (h : Meets G ω o A ∧ ¬Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' A) ∧
    ¬HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  refine ⟨meets_to_stars G h.1, ?_⟩
  intro ht
  obtain ⟨_,_,hc⟩ := h.1
  exact h.2 (meets_of_stars G hc.1 ht)

end Site

theorem site_failure_comparison [Fintype V] (G : SimpleGraph V)
    (p : V → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Site.Meets G ω a T)) :
    eventProb p (fun ω => Site.Meets G ω o A ∧ ¬Site.Meets G ω o T) ≤ b := by
  apply (eventProb_mono p _ _ (fun _ => Site.failure_subset_hyperedge G)).trans
  apply failure_comparison (Site.stars G) p (Sum.inl o) (Sum.inl '' A) (Sum.inl '' T) b hb0
  rintro _ ⟨a,ha,rfl⟩
  exact (hb a ha).trans (eventProb_mono p _ _ (fun _ => Site.meets_to_stars G))

end HyperedgeComparison

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical MeasureTheory ProbabilityTheory

/-- An unoriented nearest-neighbor bond, in its unique positive-axis indexing. -/
def Incidence (e : Bond) (x y : Vertex) : Prop :=
  (x = e.1 ∧ y = step e.1 e.2) ∨ (y = e.1 ∧ x = step e.1 e.2)

theorem step_ne (x : Vertex) (i : Fin 3) : step x i ≠ x := by
  intro h
  have := congrFun h i
  simp [step] at this

theorem incidence_symm {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    Incidence e y x := h.symm

theorem incidence_ne {e : Bond} {x y : Vertex} (h : Incidence e x y) : x ≠ y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (step_ne _ _).symm
  · exact step_ne _ _

theorem incidence_neighbor {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    NearestNeighbor x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e.2,Or.inl rfl⟩
  · exact ⟨e.2,Or.inr rfl⟩

structure LatticeGraph where
  vertices : Finset Vertex
  edges : Finset Bond
  left_mem : ∀ e ∈ edges, e.1 ∈ vertices
  right_mem : ∀ e ∈ edges, step e.1 e.2 ∈ vertices

namespace LatticeGraph
variable (G : LatticeGraph)

abbrev Node := G.vertices

noncomputable def graph : SimpleGraph G.Node where
  Adj x y := ∃ e ∈ G.edges, Incidence e x y
  symm := ⟨by rintro x y ⟨e,he,h⟩; exact ⟨e,he,incidence_symm h⟩⟩
  loopless := ⟨by rintro x ⟨e,_,h⟩; exact incidence_ne h rfl⟩

noncomputable def hypergraph : HyperedgeComparison.Hypergraph G.Node G.edges :=
  fun e x => x.1 = e.1.1 ∨ x.1 = step e.1.1 e.1.2

def BondAdj (ω : BondConfig) (x y : G.Node) : Prop :=
  ∃ e ∈ G.edges, Incidence e x y ∧ ω e = true

def BondConn (ω : BondConfig) (x y : G.Node) : Prop :=
  Relation.ReflTransGen (G.BondAdj ω) x y

def SiteConn (ω : SiteConfig) (x y : G.Node) : Prop :=
  HyperedgeComparison.Site.Connected G.graph (fun z => ω z.1) x y

def BondMeets (ω : BondConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.BondConn ω o y

def SiteMeets (ω : SiteConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.SiteConn ω o y

theorem bondAdj_open {ω : BondConfig} {x y : G.Node} (h : G.BondAdj ω x y) :
    BondOpen ω x.1 y.1 := by
  obtain ⟨e,_,h,he⟩ := h
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact Or.inl ⟨e.2,by simpa [hx] using hy,by simpa [hx] using he⟩
  · exact Or.inr ⟨e.2,by simpa [hy] using hx,by simpa [hy] using he⟩

theorem bondConn_global {ω : BondConfig} {x y : G.Node} (h : G.BondConn ω x y) :
    BondConnected ω x.1 y.1 := by
  exact h.lift Subtype.val (fun _ _ h => G.bondAdj_open h)

theorem siteConn_global {ω : SiteConfig} {x y : G.Node} (h : G.SiteConn ω x y) :
    SiteConnected ω x.1 y.1 := by
  refine ⟨h.1,h.2.lift Subtype.val ?_⟩
  intro a b hab
  obtain ⟨⟨e,_,he⟩,ha,hb⟩ := hab
  exact ⟨incidence_neighbor he,ha,hb⟩

theorem bondAdj_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondAdj ω' x y ↔ G.BondAdj ω x y := by
  constructor <;> rintro ⟨e,he,hxy,ho⟩
  · exact ⟨e,he,hxy,(h e he) ▸ ho⟩
  · exact ⟨e,he,hxy,(h e he).symm ▸ ho⟩

theorem bondConn_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondConn ω' x y ↔ G.BondConn ω x y := by
  have he : G.BondAdj ω' = G.BondAdj ω := by
    funext a b; exact propext (G.bondAdj_determined ω ω' h a b)
  simp only [BondConn,he]

theorem siteConn_determined (ω ω' : SiteConfig)
    (h : ∀ x ∈ G.vertices, ω' x = ω x) (x y : G.Node) :
    G.SiteConn ω' x y ↔ G.SiteConn ω x y := by
  have he : (fun z : G.Node => ω' z.1) = fun z => ω z.1 := by
    funext z; exact h z.1 z.2
  simp only [SiteConn,he]

theorem bondMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.edges (fun ω => G.BondMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.bondConn_determined ω ω' h o y)))

theorem siteMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.vertices (fun ω => G.SiteMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.siteConn_determined ω ω' h o y)))

theorem bondConn_iff_hypergraph (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by
  constructor
  · intro h
    apply Relation.ReflTransGen.mono (r := G.BondAdj ω) (p := _) ?_ x y h
    intro a b hab
    obtain ⟨e,he,hxy,ho⟩ := hab
    refine ⟨⟨e,he⟩,ho,Set.disjoint_empty _,?_,?_⟩
    · rcases hxy with ⟨h,_⟩ | ⟨_,h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases hxy with ⟨_,h⟩ | ⟨h,_⟩
      · exact Or.inr h
      · exact Or.inl h
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨e,ho,_,ha,hb⟩ := hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih
      · exact ih.tail ⟨e.1,e.2,Or.inl ⟨ha,hb⟩,ho⟩
      · exact ih.tail ⟨e.1,e.2,Or.inr ⟨hb,ha⟩,ho⟩
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih

/-- Pulling the actual bond connection event down to its finite bit set. -/
theorem bondMeets_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o T} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T}) := by
  rw [Measure.real_def,ProductCylinder.probability_determined G.edges p {ω | G.BondMeets ω o T}
    (fun ω ω' h => eq_iff_iff.mp (G.bondMeets_determined o T ω ω' h))]
  rw [HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  change (∃ y : G.Node, y.1 ∈ T ∧ G.BondConn (ProductCylinder.extend G.edges ξ) o y) ↔ _
  simp only [G.bondConn_iff_hypergraph]
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend,e.2]
  rw [he]
  rfl

theorem siteMeets_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o T} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T}) := by
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | G.SiteMeets ω o T}
    (fun ω ω' h => eq_iff_iff.mp (G.siteMeets_determined o T ω ω' h))]
  rw [HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]

/-- Any observable of the finite graph's connections is a finite cylinder. -/
theorem bondObservable_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.BondMeets ω)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.edges, ω' e = ω e) →
      (φ (G.BondMeets ω') ↔ φ (G.BondMeets ω)) := by
    intro ω ω' he
    have hm : G.BondMeets ω' = G.BondMeets ω := by
      funext o T; exact G.bondMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.edges p {ω | φ (G.BondMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend,e.2]
  have hm : G.BondMeets (ProductCylinder.extend G.edges ξ) =
      fun o T => HyperedgeComparison.Meets G.hypergraph ξ ∅ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [BondMeets,G.bondConn_iff_hypergraph,he,
      HyperedgeComparison.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]

theorem siteObservable_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.SiteMeets ω)} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.vertices, ω' e = ω e) →
      (φ (G.SiteMeets ω') ↔ φ (G.SiteMeets ω)) := by
    intro ω ω' he
    have hm : G.SiteMeets ω' = G.SiteMeets ω := by
      funext o T; exact G.siteMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | φ (G.SiteMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  have hm : G.SiteMeets (ProductCylinder.extend G.vertices ξ) =
      fun o T => HyperedgeComparison.Site.Meets G.graph ξ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]

/-- The comparison is now attached to actual finite lattice bond paths and
arbitrary independent laws on the entire lattice, not an assumed interface. -/
theorem bond_failure_comparison (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.BondMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o A ∧ ¬G.BondMeets ω o T} ≤ b := by
  rw [G.bondObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.bondMeets_probability] using hb a ha

theorem site_failure_comparison (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.SiteMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o A ∧ ¬G.SiteMeets ω o T} ≤ b := by
  rw [G.siteObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.site_failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.siteMeets_probability] using hb a ha

end LatticeGraph
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

structure Box where
  lower : Vertex
  upper : Vertex
  ordered : lower ≤ upper

namespace Box

@[ext] theorem ext {B C : Box} (hl : B.lower = C.lower) (hu : B.upper = C.upper) : B = C := by
  cases B; cases C; cases hl; cases hu; rfl

noncomputable def vertices (B : Box) : Finset Vertex := Finset.Icc B.lower B.upper

def Contains (B : Box) (x : Vertex) : Prop := ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

@[simp] theorem mem_vertices (B : Box) (x : Vertex) : x ∈ B.vertices ↔ B.Contains x := by
  simp only [vertices, Finset.mem_Icc, Pi.le_def, Contains]
  exact ⟨fun h i => ⟨h.1 i,h.2 i⟩,fun h => ⟨fun i => (h i).1,fun i => (h i).2⟩⟩

noncomputable def bonds (B : Box) : Finset Bond :=
  (B.vertices ×ˢ Finset.univ).filter (fun e => B.Contains (step e.1 e.2))

@[simp] theorem mem_bonds (B : Box) (e : Bond) :
    e ∈ B.bonds ↔ B.Contains e.1 ∧ B.Contains (step e.1 e.2) := by
  simp [bonds]

def expand (B : Box) (j : ℕ) : Box where
  lower := fun i => B.lower i-j
  upper := fun i => B.upper i+j
  ordered := fun i => by
    have h : B.lower i ≤ B.upper i := B.ordered i
    dsimp
    omega

def cube (c : Vertex) (m : ℕ) : Box where
  lower := fun i => c i-m
  upper := fun i => c i+m
  ordered := fun i => by dsimp; omega

@[simp] theorem contains_cube (c x : Vertex) (m : ℕ) :
    (cube c m).Contains x ↔ ∀ i, |x i-c i| ≤ (m : ℤ) := by
  simp only [Contains,cube,abs_le]
  constructor <;> intro h i <;> have hi := h i <;> omega

theorem contains_expand (B : Box) (j : ℕ) {x : Vertex} (h : B.Contains x) :
    (B.expand j).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j
  omega

theorem expand_mono (B : Box) {j k : ℕ} (hjk : j ≤ k) {x : Vertex}
    (h : (B.expand j).Contains x) : (B.expand k).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j at hi
  change B.lower i-k ≤ x i ∧ x i ≤ B.upper i+k
  omega

@[simp] theorem expand_expand (B : Box) (j k : ℕ) : (B.expand j).expand k = B.expand (j+k) := by
  apply Box.ext <;> funext i <;> simp [expand] <;> omega

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

theorem neighbor_distance {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) :
    |y i-x i| ≤ 1 := by
  obtain ⟨k,hk,he⟩ := neighbor_coordinates h
  by_cases hik : i = k
  · simp [hik,hk]
  · simp [he i hik]

theorem neighbor_in_expand (B : Box) {x y : Vertex}
    (hx : B.Contains x) (hxy : NearestNeighbor x y) : (B.expand 1).Contains y := by
  intro i
  have hi := hx i
  have hd := neighbor_distance hxy i
  rw [abs_le] at hd
  change B.lower i-1 ≤ y i ∧ y i ≤ B.upper i+1
  omega

/-- The uniqueness used by the shell-closing argument, including corners. -/
theorem exterior_neighbor_unique (B : Box) {y z z' : Vertex}
    (hy : ¬ B.Contains y) (hz : B.Contains z) (hz' : B.Contains z')
    (hyz : NearestNeighbor y z) (hyz' : NearestNeighbor y z') : z = z' := by
  obtain ⟨i,hi⟩ : ∃ i, ¬ (B.lower i ≤ y i ∧ y i ≤ B.upper i) := by
    simpa only [Contains,not_forall] using hy
  obtain ⟨j,hj,hej⟩ := neighbor_coordinates hyz
  obtain ⟨k,hk,hek⟩ := neighbor_coordinates hyz'
  have hij : i = j := by
    by_contra h
    have hh := hej i h
    have hh' := hz i
    omega
  have hik : i = k := by
    by_contra h
    have hh := hek i h
    have hh' := hz' i
    omega
  subst j; subst k
  funext l
  by_cases hl : l = i
  · subst l
    have hz0 := hz i
    have hz1 := hz' i
    have hj0 := hj.le
    have hk0 := hk.le
    rw [abs_le] at hj0 hk0
    omega
  · rw [hej l hl,hek l hl]

def seedCenter (C : Box) (m : ℕ) (z : Vertex) : Vertex :=
  fun i => max (C.lower i+m) (min (C.upper i-m) (z i))

theorem seedCenter_bounds (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) (i : Fin 3) :
    C.lower i+m ≤ C.seedCenter m z i ∧ C.seedCenter m z i ≤ C.upper i-m := by
  exact ⟨le_max_left _ _,max_le (hw i) (min_le_left _ _)⟩

theorem seed_contained (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) (z : Vertex) :
    ∀ x, (cube (C.seedCenter m z) m).Contains x → C.Contains x := by
  intro x hx i
  have hb := C.seedCenter_bounds m hw z i
  have hx0 := (contains_cube _ _ _).mp hx i
  rw [abs_le] at hx0
  omega

theorem seed_contains_entry (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z : Vertex} (hz : C.Contains z) :
    (cube (C.seedCenter m z) m).Contains z := by
  rw [contains_cube]
  intro i
  have hi := hz i
  have hwi := hw i
  dsimp [seedCenter]
  rw [abs_le]
  omega

theorem seed_center_near (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z y : Vertex}
    (hz : C.Contains z) (hyz : NearestNeighbor y z) (i : Fin 3) :
    |C.seedCenter m z i-y i| ≤ (m : ℤ)+1 := by
  have h1 := (contains_cube _ _ _).mp (C.seed_contains_entry m hw hz) i
  have h2 := neighbor_distance hyz i
  rw [abs_le] at h1 h2 ⊢
  omega

theorem expanded_seed_width (B : Box) {m j : ℕ} (hmj : m ≤ j) (i : Fin 3) :
    (B.expand j).lower i+m ≤ (B.expand j).upper i-m := by
  have h : B.lower i ≤ B.upper i := B.ordered i
  dsimp [expand]
  omega

/-- The exact number of candidates excluded in one greedy selection. -/
theorem card_cube (c : Vertex) (m : ℕ) : (cube c m).vertices.card = (2*m+1)^3 := by
  rw [vertices,Pi.card_Icc]
  have he (i : Fin 3) : (Finset.Icc ((cube c m).lower i) ((cube c m).upper i)).card = 2*m+1 := by
    rw [Int.card_Icc]
    dsimp [cube]
    omega
  simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem disjoint_seeds {a b : Vertex} {m : ℕ}
    (h : ∃ i, (2*m : ℤ) < |a i-b i|) :
    Disjoint (cube a m).vertices (cube b m).vertices := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨i,hi⟩ := h
  have ha := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxa) i
  have hb := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxb) i
  rw [abs_le] at ha hb
  have hab : |a i-b i| ≤ 2*m := by rw [abs_le]; omega
  omega

theorem separated_subset (s : Finset Vertex) (m K : ℕ)
    (hcard : K*(8*m+5)^3 ≤ s.card) :
    ∃ t ⊆ s, t.card = K ∧
      ∀ a ∈ t, ∀ b ∈ t, a ≠ b → ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
  induction K generalizing s with
  | zero => exact ⟨∅,Finset.empty_subset s,rfl,by simp⟩
  | succ K ih =>
    have hcpos : 0 < (8*m+5)^3 := by positivity
    have hspos : 0 < s.card := by nlinarith
    obtain ⟨a,ha⟩ := Finset.card_pos.mp hspos
    let U := (cube a (4*m+2)).vertices
    have hU : U.card = (8*m+5)^3 := by
      rw [card_cube]
      congr 1
      omega
    have hc : (s ∩ U).card ≤ (8*m+5)^3 := by
      rw [←hU]
      exact Finset.card_le_card Finset.inter_subset_right
    have hdiff : K*(8*m+5)^3 ≤ (s \ U).card := by
      have he := Finset.card_sdiff_add_card_inter s U
      rw [Nat.succ_mul] at hcard
      omega
    obtain ⟨t,ht,htc,hts⟩ := ih (s \ U) hdiff
    have hat : a ∉ t := by
      intro hat
      have haa := (Finset.mem_sdiff.mp (ht hat)).2
      apply haa
      apply (mem_vertices _ _).mpr
      rw [contains_cube]
      intro i
      simp only [sub_self,abs_zero]
      positivity
    have has (b : Vertex) (hb : b ∈ t) : ∃ i, (4*m+2 : ℤ) < |a i-b i| := by
      have hn := (Finset.mem_sdiff.mp (ht hb)).2
      have hn' : ¬ ∀ i, |b i-a i| ≤ (4*m+2 : ℤ) := by
        simpa [U,contains_cube] using hn
      push Not at hn'
      simpa only [abs_sub_comm] using hn'
    refine ⟨insert a t,?_,by simp [hat,htc],?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ha
      · exact (Finset.mem_sdiff.mp (ht hb)).1
    · intro b hb c hc hbc
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · exact (hbc rfl).elim
        · exact has c hc
      · rcases Finset.mem_insert.mp hc with hca | hc
        · subst c
          simpa only [abs_sub_comm] using has b hb
        · exact hts b hb c hc hbc

theorem separated_centers (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {y y' z z' : Vertex}
    (hz : C.Contains z) (hz' : C.Contains z')
    (hy : NearestNeighbor y z) (hy' : NearestNeighbor y' z')
    (hsep : ∃ i, (4*m+2 : ℤ) < |y i-y' i|) :
    ∃ i, (2*m : ℤ) < |C.seedCenter m z i-C.seedCenter m z' i| := by
  obtain ⟨i,hi⟩ := hsep
  refine ⟨i,?_⟩
  have h1 := C.seed_center_near m hw hz hy i
  have h2 := C.seed_center_near m hw hz' hy' i
  by_contra! hbad
  rw [abs_le] at h1 h2 hbad
  have hh : |y i-y' i| ≤ 4*m+2 := by rw [abs_le]; omega
  omega

def translateVertex (c x : Vertex) : Vertex := fun i => x i+c i

def translateBond (c : Vertex) (e : Bond) : Bond := (translateVertex c e.1,e.2)

theorem translateVertex_injective (c : Vertex) : Function.Injective (translateVertex c) := by
  intro x y h
  funext i
  have hi := congrFun h i
  dsimp [translateVertex] at hi
  omega

theorem translateBond_injective (c : Vertex) : Function.Injective (translateBond c) := by
  intro e e' h
  have h1 : e.1 = e'.1 := translateVertex_injective c (congrArg Prod.fst h)
  have h2 : e.2 = e'.2 := by simpa only [translateBond] using congrArg Prod.snd h
  exact Prod.ext h1 h2

@[simp] theorem step_translate (c x : Vertex) (i : Fin 3) :
    step (translateVertex c x) i = translateVertex c (step x i) := by
  funext j
  dsimp [step,translateVertex]
  omega

@[simp] theorem cube_contains_translate (c x : Vertex) (m : ℕ) :
    (cube c m).Contains (translateVertex c x) ↔ (cube 0 m).Contains x := by
  simp [contains_cube,translateVertex]

theorem cube_vertices_translate (c : Vertex) (m : ℕ) :
    (cube c m).vertices = (cube 0 m).vertices.image (translateVertex c) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_image.mpr ⟨fun i => x i-c i,?_,?_⟩
    · rw [mem_vertices,contains_cube]
      simpa using (contains_cube _ _ _).mp ((mem_vertices _ _).mp hx)
    · funext i; simp [translateVertex]
  · rintro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa [translateVertex] using hy

theorem cube_bonds_translate (c : Vertex) (m : ℕ) :
    (cube c m).bonds = (cube 0 m).bonds.image (translateBond c) := by
  ext e
  constructor
  · intro he
    let e' : Bond := (fun i => e.1 i-c i,e.2)
    have heq : translateBond c e' = e := by
      apply Prod.ext
      · funext i; simp [translateBond,translateVertex,e']
      · rfl
    refine Finset.mem_image.mpr ⟨e',?_,heq⟩
    rw [←heq,mem_bonds] at he
    simpa [translateBond,translateVertex] using he
  · intro he
    obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
    simpa [translateBond,translateVertex] using he'

theorem cube_bonds_card (c : Vertex) (m : ℕ) :
    (cube c m).bonds.card = (cube 0 m).bonds.card := by
  rw [cube_bonds_translate,Finset.card_image_of_injective _ (translateBond_injective c)]

def Within (B : Box) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ B.Contains x ∧ B.Contains y

theorem within_symm (B : Box) {x y : Vertex} (h : B.Within x y) : B.Within y x := by
  obtain ⟨⟨i,hi⟩,hx,hy⟩ := h
  exact ⟨⟨i,hi.symm⟩,hy,hx⟩

theorem within_path_symm (B : Box) {x y : Vertex}
    (h : Relation.ReflTransGen B.Within x y) : Relation.ReflTransGen B.Within y x := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact .head (B.within_symm hab) ih

theorem line_step (x : Vertex) (i : Fin 3) (n : ℤ) :
    Function.update x i (n+1) = step (Function.update x i n) i := by
  funext j
  by_cases hj : j = i
  · subst j; simp [step]
  · simp [step,hj,Ne.symm hj]

theorem line_contains (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    (n : ℤ) (hn : B.lower i ≤ n ∧ n ≤ B.upper i) : B.Contains (Function.update x i n) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using hn
  · simpa [Function.update_of_ne hj] using hx j

theorem line_path_le (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {a b : ℤ} (ha : B.lower i ≤ a) (hb : b ≤ B.upper i) (hab : a ≤ b) :
    Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i b) := by
  have hh (n : ℤ) (han : a ≤ n) : n ≤ b →
      Relation.ReflTransGen B.Within (Function.update x i a) (Function.update x i n) := by
    induction n,han using Int.leInduction with
    | base => intro _; exact .refl
    | succ n han ih =>
      intro hn
      apply (ih (by omega)).tail
      exact ⟨⟨i,Or.inl (line_step x i n)⟩,
        B.line_contains hx i n ⟨by omega,by omega⟩,
        B.line_contains hx i (n+1) ⟨by omega,by omega⟩⟩
  exact hh b hab le_rfl

theorem line_path (B : Box) {x : Vertex} (hx : B.Contains x) (i : Fin 3)
    {b : ℤ} (hb : B.lower i ≤ b ∧ b ≤ B.upper i) :
    Relation.ReflTransGen B.Within x (Function.update x i b) := by
  have hx' := hx i
  by_cases h : x i ≤ b
  · simpa using B.line_path_le hx i hx'.1 hb.2 h
  · apply B.within_path_symm
    simpa using B.line_path_le hx i hb.1 hx'.2 (le_of_not_ge h)

/-- Every nonempty integer rectangle is nearest-neighbor connected internally. -/
theorem connected (B : Box) {x y : Vertex} (hx : B.Contains x) (hy : B.Contains y) :
    Relation.ReflTransGen B.Within x y := by
  let patch (s : Finset (Fin 3)) : Vertex := fun i => if i ∈ s then y i else x i
  have hp (s : Finset (Fin 3)) : B.Contains (patch s) := by
    intro i
    by_cases hi : i ∈ s
    · simpa [patch,hi] using hy i
    · simpa [patch,hi] using hx i
  have hc (s : Finset (Fin 3)) : Relation.ReflTransGen B.Within x (patch s) := by
    induction s using Finset.induction_on with
    | empty => simpa only [patch,Finset.notMem_empty,ite_false] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen B.Within x x)
    | @insert i s hi ih =>
      have he : patch (insert i s) = Function.update (patch s) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [patch]
        · simp [patch,hj]
      rw [he]
      exact ih.trans (B.line_path (hp s) i (hy i))
  simpa only [patch,Finset.mem_univ,ite_true] using hc Finset.univ

end Box
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

inductive Model | bond | site

namespace Model
abbrev Bit : Model → Type
  | bond => Bond
  | site => Vertex
abbrev Config (m : Model) := m.Bit → Bool
instance (m : Model) : Countable m.Bit := by cases m <;> infer_instance
instance (m : Model) : DecidableEq m.Bit := by cases m <;> infer_instance
end Model

namespace Box
noncomputable def bits (B : Box) : (m : Model) → Finset m.Bit
  | .bond => B.bonds
  | .site => B.vertices
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
noncomputable def bits : (m : Model) → Finset m.Bit
  | .bond => G.edges
  | .site => G.vertices

def Open : (m : Model) → m.Config → G.Node → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x.1 = true

def Adj : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondAdj ω x y
  | .site,ω,x,y => G.graph.Adj x y ∧ ω x.1 = true ∧ ω y.1 = true

def Conn : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondConn ω x y
  | .site,ω,x,y => G.SiteConn ω x y

def Meets (m : Model) (ω : m.Config) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.Conn m ω o y

theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl

theorem adj_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  cases m
  · exact ⟨trivial,trivial⟩
  · exact h.2

theorem adj_neighbor (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    NearestNeighbor x.1 y.1 := by
  cases m
  · obtain ⟨e,_,he,_⟩ := h; exact incidence_neighbor he
  · obtain ⟨⟨e,_,he⟩,_⟩ := h; exact incidence_neighbor he

theorem adj_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Adj m ω y x := by
  cases m
  · obtain ⟨e,he,hi,ho⟩ := h; exact ⟨e,he,incidence_symm hi,ho⟩
  · exact ⟨G.graph.adj_symm h.1,h.2.2,h.2.1⟩

theorem conn_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  obtain ⟨hx,h⟩ := (G.conn_iff m ω x y).mp h
  refine ⟨hx,?_⟩
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact (G.adj_open m hab).2

theorem conn_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Conn m ω y x := by
  refine (G.conn_iff m ω y x).mpr ⟨(G.conn_open m h).2,?_⟩
  have hh := (G.conn_iff m ω x y).mp h |>.2
  clear h
  induction hh with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head (G.adj_symm m hab)

theorem conn_trans (m : Model) {ω : m.Config} {x y z : G.Node}
    (h : G.Conn m ω x y) (h' : G.Conn m ω y z) : G.Conn m ω x z := by
  exact (G.conn_iff m ω x z).mpr ⟨((G.conn_iff m ω x y).mp h).1,
    ((G.conn_iff m ω x y).mp h).2.trans ((G.conn_iff m ω y z).mp h').2⟩

theorem conn_adj (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Conn m ω x y := (G.conn_iff m ω x y).mpr ⟨(G.adj_open m h).1,.single h⟩

theorem conn_determined (m : Model) (ω ω' : m.Config)
    (h : ∀ e ∈ G.bits m, ω' e = ω e) (x y : G.Node) :
    G.Conn m ω' x y ↔ G.Conn m ω x y := by
  cases m
  · exact G.bondConn_determined ω ω' h x y
  · exact G.siteConn_determined ω ω' h x y

theorem meets_determined (m : Model) (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) (G.bits m) (fun ω => G.Meets m ω o T) := by
  intro ω ω' h
  apply propext
  simp only [Meets,G.conn_determined m ω ω' h]

theorem measurableSet_meets (m : Model) (o : G.Node) (T : Set Vertex) :
    MeasurableSet {ω | G.Meets m ω o T} :=
  ProductCylinder.measurableSet_determined _ _ (fun ω ω' h =>
    eq_iff_iff.mp (G.meets_determined m o T ω ω' h))

theorem failure_comparison (m : Model) (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.Meets m ω a T}) :
    (ProductCylinder.law p).real {ω | G.Meets m ω o A ∧ ¬G.Meets m ω o T} ≤ b := by
  cases m
  · exact G.bond_failure_comparison p o A T hb0 hb
  · exact G.site_failure_comparison p o A T hb0 hb

def ContainsBox (B : Box) : Prop := B.vertices ⊆ G.vertices ∧ B.bonds ⊆ G.edges

theorem containsBox_node {B : Box} (h : G.ContainsBox B) {x : Vertex}
    (hx : B.Contains x) : x ∈ G.vertices := h.1 ((B.mem_vertices x).mpr hx)

theorem neighbor_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ e : Bond, Incidence e x y := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨(x,i),Or.inl ⟨rfl,h⟩⟩
  · exact ⟨(y,i),Or.inr ⟨rfl,h⟩⟩

theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

theorem open_box_adj (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : NearestNeighbor x.1 y.1) :
    G.Adj m ω x y := by
  obtain ⟨e,he⟩ := neighbor_incidence hxy
  have heb := incidence_internal hx hy he
  cases m
  · exact ⟨e,hB.2 heb,he,ho e heb⟩
  · exact ⟨⟨e,hB.2 heb,he⟩,ho x.1 ((B.mem_vertices x.1).mpr hx),
      ho y.1 ((B.mem_vertices y.1).mpr hy)⟩

/-- Lifting a vertex path into a finite graph, retaining the exact endpoints. -/
theorem lift_path {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have hh : ∀ {z : Vertex}, Relation.ReflTransGen r x.1 z →
      ∀ hz : z ∈ G.vertices, Relation.ReflTransGen s x ⟨z,hz⟩ := by
    intro z hp
    induction hp with
    | refl => intro _; exact .refl
    | @tail a b ha hab ih =>
      intro hb
      rcases ha.cases_tail with hxa | ⟨u,hu,hua⟩
      · subst a
        exact Relation.ReflTransGen.single (hrel x ⟨b,hb⟩ hab)
      · have ham := hmem u a hua
        exact (ih ham).tail (hrel ⟨a,ham⟩ ⟨b,hb⟩ hab)
  exact hh h y.2

theorem open_box_conn (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) : G.Conn m ω x y := by
  apply (G.conn_iff m ω x y).mpr
  constructor
  · cases m
    · trivial
    · exact ho x.1 ((B.mem_vertices x.1).mpr hx)
  · apply G.lift_path (r := B.Within)
      (fun _ _ h => G.containsBox_node hB h.2.2)
      (fun x y h => G.open_box_adj m hB ho h.2.1 h.2.2 h.1)
    exact B.connected hx hy

end LatticeGraph
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem step_ge (x : Vertex) (i : Fin 3) : x ≤ step x i := by
  intro j; simp only [step]; split_ifs <;> omega

theorem step_direction_injective (x : Vertex) : Function.Injective (step x) := by
  intro i j h
  by_contra hij
  have hh := congrFun h i
  simp only [step,ite_true,ite_eq_right (Ne.symm hij),add_zero] at hh
  omega

theorem step_no_reverse (x y : Vertex) (i j : Fin 3)
    (h : y = step x i) : x ≠ step y j := by
  intro hh
  have hle : y i ≤ x i := by rw [hh]; exact step_ge y j i
  have hlt : x i < y i := by simp [h,step]
  exact not_lt_of_ge hle hlt

theorem incidence_unique {e f : Bond} {x y : Vertex}
    (he : Incidence e x y) (hf : Incidence f x y) : e = f := by
  rcases he with ⟨hx,hy⟩ | ⟨hy,hx⟩ <;> rcases hf with ⟨hx',hy'⟩ | ⟨hy',hx'⟩
  · apply Prod.ext
    · exact hx.symm.trans hx'
    · apply step_direction_injective x
      simpa only [←hx,←hx'] using hy.symm.trans hy'
  · exact False.elim (step_no_reverse x y e.2 f.2 (by simpa [←hx] using hy)
      (by simpa [←hy'] using hx'))
  · exact False.elim (step_no_reverse y x e.2 f.2 (by simpa [←hy] using hx)
      (by simpa [←hx'] using hy'))
  · apply Prod.ext
    · exact hy.symm.trans hy'
    · apply step_direction_injective y
      simpa only [←hy,←hy'] using hx.symm.trans hx'

noncomputable def neighborBond (x y : Vertex) : Bond :=
  if h : NearestNeighbor x y then (LatticeGraph.neighbor_incidence h).choose else (x,0)

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

theorem neighborBond_eq {e : Bond} {x y : Vertex} (he : Incidence e x y) :
    neighborBond x y = e := incidence_unique (neighborBond_incidence (incidence_neighbor he)) he

namespace Box

def Exterior (C : Box) (y : Vertex) : Prop :=
  ¬C.Contains y ∧ ∃ z, C.Contains z ∧ NearestNeighbor y z

noncomputable def entry (C : Box) (y : Vertex) : Vertex :=
  if h : C.Exterior y then h.2.choose else C.lower

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

theorem entry_eq {C : Box} {y z : Vertex} (hy : ¬C.Contains y)
    (hz : C.Contains z) (h : NearestNeighbor y z) : C.entry y = z := by
  have hey : C.Exterior y := ⟨hy,z,hz,h⟩
  exact C.exterior_neighbor_unique hy (entry_spec hey).1 hz (entry_spec hey).2 h

noncomputable def entryBit (C : Box) : (m : Model) → Vertex → m.Bit
  | .bond,y => neighborBond y (C.entry y)
  | .site,y => C.entry y

theorem exterior_expand {C : Box} {y : Vertex} (h : C.Exterior y) :
    (C.expand 1).Contains y := by
  obtain ⟨z,hz,hzy⟩ := h.2
  apply C.neighbor_in_expand hz
  obtain ⟨i,hi | hi⟩ := hzy
  · exact ⟨i,Or.inr hi⟩
  · exact ⟨i,Or.inl hi⟩

theorem entryBit_internal (m : Model) {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  have he := C.contains_expand 1 (entry_spec h).1
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand h) he
      (neighborBond_incidence (entry_spec h).2)
  · exact (mem_vertices _ _).mpr he

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

def OutsideAdj (m : Model) (C : Box) (ω : m.Config) (x y : G.Node) : Prop :=
  ¬C.Contains x.1 ∧ ¬C.Contains y.1 ∧ G.Adj m ω x y

def OutsideReach (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) : Prop :=
  ¬C.Contains o.1 ∧ G.Open m ω o ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o y

noncomputable def entrants (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset Vertex :=
  G.vertices.filter (fun y => ∃ hy : y ∈ G.vertices,
    C.Exterior y ∧ G.OutsideReach m C ω o ⟨y,hy⟩)

@[simp] theorem mem_entrants (m : Model) (C : Box) (ω : m.Config) (o y : G.Node) :
    y.1 ∈ G.entrants m C ω o ↔ C.Exterior y.1 ∧ G.OutsideReach m C ω o y := by
  simp only [entrants,Finset.mem_filter,y.2,true_and]
  exact ⟨fun ⟨_,h⟩ => h,fun h => ⟨trivial,h⟩⟩

theorem outsideReach_conn (m : Model) {C : Box} {ω : m.Config} {o y : G.Node}
    (h : G.OutsideReach m C ω o y) : G.Conn m ω o y :=
  (G.conn_iff m ω o y).mpr ⟨h.2.1,Relation.ReflTransGen.mono (fun _ _ (hh : G.OutsideAdj m C ω _ _) => hh.2.2) o y h.2.2⟩

theorem first_entry (m : Model) {C : Box} {ω : m.Config} {o z : G.Node}
    (ho : ¬C.Contains o.1) (hz : C.Contains z.1) (h : G.Conn m ω o z) :
    ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
  have hp := ((G.conn_iff m ω o z).mp h).2
  have hop := ((G.conn_iff m ω o z).mp h).1
  have hh : ∀ {x : G.Node}, Relation.ReflTransGen (G.Adj m ω) o x →
      (¬C.Contains x.1 ∧ Relation.ReflTransGen (G.OutsideAdj m C ω) o x) ∨
      ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ⟨ho,.refl⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hi⟩ | he
      · by_cases hb : C.Contains b.1
        · exact Or.inr ⟨a,b,(G.mem_entrants m C ω o a).mpr
            ⟨⟨ha,b.1,hb,G.adj_neighbor m hab⟩,ho,hop,hi⟩,hb,hab⟩
        · exact Or.inl ⟨hb,hi.tail ⟨ha,hb,hab⟩⟩
      · exact Or.inr he
  exact (hh hp).resolve_left (fun h => h.1 hz)

theorem meets_entrants_nonempty (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (h : G.Meets m ω o {x | C.Contains x}) :
    (G.entrants m C ω o).Nonempty := by
  obtain ⟨z,hz,hz'⟩ := h
  obtain ⟨y,w,hy,_,_⟩ := G.first_entry m ho hz hz'
  exact ⟨y.1,hy⟩

theorem entryBit_open (m : Model) {C : Box} {ω : m.Config} {y z : G.Node}
    (hy : ¬C.Contains y.1) (hz : C.Contains z.1) (h : G.Adj m ω y z) :
    ω (C.entryBit m y.1) = true := by
  have he := C.entry_eq hy hz (G.adj_neighbor m h)
  cases m
  · obtain ⟨e,_,hi,ho⟩ := h
    simpa only [Box.entryBit,he,neighborBond_eq hi] using ho
  · simpa only [Box.entryBit,he] using h.2.2

noncomputable def entryBits (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Finset m.Bit :=
  (G.entrants m C ω o).image (C.entryBit m)

def Blocked (m : Model) (C : Box) (ω : m.Config) (o : G.Node) : Prop :=
  ∀ e ∈ G.entryBits m C ω o, ω e = false

theorem entryBits_card (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    (G.entryBits m C ω o).card ≤ (G.entrants m C ω o).card := Finset.card_image_le

theorem blocked_not_meets (m : Model) {C : Box} {ω : m.Config} {o : G.Node}
    (ho : ¬C.Contains o.1) (hb : G.Blocked m C ω o) :
    ¬G.Meets m ω o {x | C.Contains x} := by
  rintro ⟨z,hz,hp⟩
  obtain ⟨y,w,hy,hw,hyw⟩ := G.first_entry m ho hz hp
  have hyout := ((G.mem_entrants m C ω o y).mp hy).1.1
  have hopen := G.entryBit_open m hyout hw hyw
  have hclosed := hb (C.entryBit m y.1) (Finset.mem_image.mpr ⟨y.1,hy,rfl⟩)
  exact Bool.noConfusion (hopen.symm.trans hclosed)

/-- The shell blocking events are disjoint for the actual induced-outside
paths. This is the pathwise argument, not a probabilistic assumption. -/
theorem blocked_earlier_entrants (m : Model) {B : Box} {i j : ℕ} (hij : i < j)
    {ω : m.Config} {o : G.Node} (ho : ¬(B.expand j).Contains o.1)
    (hb : G.Blocked m (B.expand j) ω o) : G.entrants m (B.expand i) ω o = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  obtain ⟨hey,hry⟩ := (G.mem_entrants m (B.expand i) ω o ⟨y,hyG⟩).mp hy
  have hyj : (B.expand j).Contains y := by
    have he := Box.exterior_expand hey
    rw [Box.expand_expand] at he
    exact B.expand_mono (by omega) he
  exact G.blocked_not_meets m ho hb ⟨⟨y,hyG⟩,hyj,G.outsideReach_conn m hry⟩

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

noncomputable def outsideBits : (m : Model) → Box → Finset m.Bit
  | .bond,C => G.edges.filter (fun e => ¬C.Contains e.1 ∧ ¬C.Contains (step e.1 e.2))
  | .site,C => G.vertices.filter (fun x => ¬C.Contains x)

theorem outsideAdj_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (x y : G.Node) :
    G.OutsideAdj m C ω' x y ↔ G.OutsideAdj m C ω x y := by
  have hh (ω ω' : m.Config) (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e)
      (ha : G.OutsideAdj m C ω' x y) : G.OutsideAdj m C ω x y := by
    refine ⟨ha.1,ha.2.1,?_⟩
    cases m
    · obtain ⟨e,he,hi,ho⟩ := ha.2.2
      refine ⟨e,he,hi,?_⟩
      have hem : e ∈ G.outsideBits .bond C := by
        apply Finset.mem_filter.mpr
        refine ⟨he,?_⟩
        rcases hi with ⟨hx,hy⟩ | ⟨hy,hx⟩
        · exact ⟨hx ▸ ha.1,hy ▸ ha.2.1⟩
        · exact ⟨hy ▸ ha.2.1,hx ▸ ha.1⟩
      rw [←h e hem]; exact ho
    · exact ⟨ha.2.2.1,(h x.1 (Finset.mem_filter.mpr ⟨x.2,ha.1⟩)) ▸ ha.2.2.2.1,
        (h y.1 (Finset.mem_filter.mpr ⟨y.2,ha.2.1⟩)) ▸ ha.2.2.2.2⟩
  exact ⟨hh ω ω' h, hh ω' ω (fun e he => (h e he).symm)⟩

theorem outsideReach_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (o y : G.Node) :
    G.OutsideReach m C ω' o y ↔ G.OutsideReach m C ω o y := by
  by_cases ho : C.Contains o.1
  · simp only [OutsideReach,ho,not_true_eq_false,false_and]
  have hr : G.OutsideAdj m C ω' = G.OutsideAdj m C ω := by
    funext x y; exact propext (G.outsideAdj_determined m C ω ω' h x y)
  have hop : G.Open m ω' o ↔ G.Open m ω o := by
    cases m
    · rfl
    · change (ω' o.1 = true) ↔ (ω o.1 = true)
      rw [h o.1 (Finset.mem_filter.mpr ⟨o.2,ho⟩)]
  simp only [OutsideReach,hr,hop]

theorem entrants_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entrants m C ω o) := by
  intro ω ω' h
  ext y
  simp only [entrants,Finset.mem_filter,G.outsideReach_determined m C ω ω' h]

theorem entryBits_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entryBits m C ω o) := by
  intro ω ω' h
  simp only [entryBits,G.entrants_determined m C o ω ω' h]

theorem outsideBits_disjoint_inside (m : Model) (C : Box) :
    Disjoint (G.outsideBits m C) (C.bits m) := by
  rw [Finset.disjoint_left]
  intro e he he'
  cases m
  · exact (Finset.mem_filter.mp he).2.1 ((Box.mem_bonds C e).mp he').1
  · exact (Finset.mem_filter.mp he).2 ((Box.mem_vertices C e).mp he')

theorem entryBit_not_outside (m : Model) {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit m y ∉ G.outsideBits m C := by
  intro he
  have hentry := (Box.entry_spec hy).1
  cases m
  · have hi := neighborBond_incidence (Box.entry_spec hy).2
    obtain ⟨_,hout,hout'⟩ := Finset.mem_filter.mp he
    rcases hi with ⟨_,hz⟩ | ⟨hz,_⟩
    · exact hout' (hz ▸ hentry)
    · exact hout (hz ▸ hentry)
  · exact (Finset.mem_filter.mp he).2 hentry

theorem entryBits_disjoint_outside (m : Model) (C : Box) (ω : m.Config) (o : G.Node) :
    Disjoint (G.entryBits m C ω o) (G.outsideBits m C) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
  have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
  exact G.entryBit_not_outside m ((G.mem_entrants m C ω o ⟨y,hyG⟩).mp hy).1 he'

end CriticalZ3.LatticeGraph

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

theorem bits_mono (m : Model) {B C : Box} (h : ∀ x, B.Contains x → C.Contains x) :
    B.bits m ⊆ C.bits m := by
  intro e he
  cases m
  · exact (mem_bonds C e).mpr ⟨h _ ((mem_bonds B e).mp he).1,h _ ((mem_bonds B e).mp he).2⟩
  · exact (mem_vertices C e).mpr (h _ ((mem_vertices B e).mp he))

theorem disjoint_bits (m : Model) {B C : Box} (h : Disjoint B.vertices C.vertices) :
    Disjoint (B.bits m) (C.bits m) := by
  rw [Finset.disjoint_left] at h ⊢
  intro e he he'
  cases m
  · exact h ((mem_vertices B e.1).mpr ((mem_bonds B e).mp he).1)
      ((mem_vertices C e.1).mpr ((mem_bonds C e).mp he').1)
  · exact h he he'

@[simp] theorem center_mem_cube (c : Vertex) (r : ℕ) : (cube c r).Contains c := by
  rw [contains_cube]; intro i; simp

theorem cube_bits_card (m : Model) (c : Vertex) (r : ℕ) :
    ((cube c r).bits m).card = ((cube 0 r).bits m).card := by
  cases m
  · exact cube_bonds_card _ _
  · simp only [bits,card_cube]

noncomputable def relayCenter (C : Box) (r : ℕ) (y : Vertex) := C.seedCenter r (C.entry y)
noncomputable def seedBox (C : Box) (r : ℕ) (y : Vertex) := cube (C.relayCenter r y) r

noncomputable def successBits (C : Box) (r : ℕ) : (m : Model) → Vertex → Finset m.Bit
  | .bond,y => insert (C.entryBit .bond y) (C.seedBox r y).bonds
  | .site,y => (C.seedBox r y).vertices

noncomputable def seedCard (m : Model) (r : ℕ) : ℕ := ((cube 0 r).bits m).card
noncomputable def successCard (m : Model) (r : ℕ) : ℕ := seedCard m r + match m with
  | .bond => 1
  | .site => 0

theorem crossing_not_internal {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit .bond y ∉ C.bonds := by
  intro he
  obtain ⟨h0,h1⟩ := (mem_bonds C _).mp he
  have hi := neighborBond_incidence (entry_spec hy).2
  rcases hi with ⟨hx,_⟩ | ⟨_,hx⟩
  · exact hy.1 (hx ▸ h0)
  · exact hy.1 (hx ▸ h1)

theorem crossing_injective {C : Box} {y z : Vertex} (hy : C.Exterior y) (hz : C.Exterior z)
    (he : C.entryBit .bond y = C.entryBit .bond z) : y = z := by
  have hi := neighborBond_incidence (entry_spec hy).2
  have hj := neighborBond_incidence (entry_spec hz).2
  change Incidence (C.entryBit .bond y) y (C.entry y) at hi
  change Incidence (C.entryBit .bond z) z (C.entry z) at hj
  rw [←he] at hj
  rcases hi with ⟨hy0,hy1⟩ | ⟨hy1,hy0⟩ <;>
    rcases hj with ⟨hz0,hz1⟩ | ⟨hz1,hz0⟩
  · exact hy0.trans hz0.symm
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact hy0.trans hz0.symm

theorem seedBox_contained (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (y : Vertex) :
    ∀ x, (C.seedBox r y).Contains x → C.Contains x := C.seed_contained r hw (C.entry y)

theorem successBits_card (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    (C.successBits r m y).card = successCard m r := by
  cases m
  · have he : C.entryBit .bond y ∉ (C.seedBox r y).bonds := fun h =>
      C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw y) h)
    rw [successBits,Finset.card_insert_of_notMem he]
    change ((cube (C.relayCenter r y) r).bits .bond).card+1 = _
    rw [cube_bits_card]; rfl
  · exact cube_bits_card .site (C.relayCenter r y) r

theorem successBits_disjoint (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y z : Vertex}
    (hy : C.Exterior y) (hz : C.Exterior z) (hsep : ∃ i, (4*r+2 : ℤ) < |y i-z i|) :
    Disjoint (C.successBits r m y) (C.successBits r m z) := by
  have hcent := C.separated_centers r hw (entry_spec hy).1 (entry_spec hz).1
    (entry_spec hy).2 (entry_spec hz).2 hsep
  have hseed := disjoint_bits m (disjoint_seeds hcent)
  have hyz : y ≠ z := by
    intro he
    obtain ⟨i,hi⟩ := hsep
    rw [he,sub_self,abs_zero] at hi
    omega
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_insert.mp he with he | he <;> rcases Finset.mem_insert.mp he' with he' | he'
    · exact hyz (C.crossing_injective hy hz (he.symm.trans he'))
    · subst e
      exact C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw z) he')
    · subst e
      exact C.crossing_not_internal hz (bits_mono .bond (C.seedBox_contained r hw y) he)
    · exact Finset.disjoint_left.mp hseed he he'
  · exact hseed

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem successBits_disjoint_outside (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    Disjoint (C.successBits r m y) (G.outsideBits m C) := by
  have hs := (G.outsideBits_disjoint_inside m C).symm.mono_left
    (Box.bits_mono m (C.seedBox_contained r hw y))
  cases m
  · rw [Box.successBits,Finset.disjoint_insert_left]
    exact ⟨G.entryBit_not_outside .bond hy,hs⟩
  · exact hs

theorem ContainsBox.mono {B C : Box} (hC : G.ContainsBox C)
    (h : ∀ x, B.Contains x → C.Contains x) : G.ContainsBox B :=
  ⟨(Box.bits_mono .site h).trans hC.1,(Box.bits_mono .bond h).trans hC.2⟩

/-- A successful exterior trial supplies a path for both bond and site percolation. -/
theorem success_reaches_center (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    {ω : m.Config} {o y : G.Node} (hy : y.1 ∈ G.entrants m C ω o)
    (hs : ∀ e ∈ C.successBits r m y.1, ω e = true) :
    ∃ v : G.Node, v.1 = C.relayCenter r y.1 ∧ G.Conn m ω o v := by
  obtain ⟨hey,hreach⟩ := (G.mem_entrants m C ω o y).mp hy
  have hCg : G.ContainsBox C := hC.mono G (fun _ => C.contains_expand 1)
  have hUg : G.ContainsBox (C.seedBox r y.1) := hCg.mono G (C.seedBox_contained r hw y.1)
  have hz := (Box.entry_spec hey).1
  let z : G.Node := ⟨C.entry y.1,G.containsBox_node hCg hz⟩
  let v : G.Node := ⟨C.relayCenter r y.1,
    G.containsBox_node hUg (Box.center_mem_cube _ _)⟩
  have heo : ∀ e ∈ (C.seedBox r y.1).bits m, ω e = true := by
    intro e he
    cases m
    · exact hs e (Finset.mem_insert_of_mem he)
    · exact hs e he
  have hyz : G.Adj m ω y z := by
    have hi := neighborBond_incidence (Box.entry_spec hey).2
    have heb := incidence_internal (Box.exterior_expand hey) (C.contains_expand 1 hz) hi
    cases m
    · exact ⟨C.entryBit .bond y.1,hC.2 heb,hi,hs _ (Finset.mem_insert_self _ _)⟩
    · exact ⟨⟨neighborBond y.1 z.1,hC.2 heb,hi⟩,(G.conn_open .site (G.outsideReach_conn .site hreach)).2,
        heo _ ((Box.mem_vertices _ _).mpr (C.seed_contains_entry r hw hz))⟩
  refine ⟨v,rfl,G.conn_trans m (G.outsideReach_conn m hreach) ?_⟩
  exact G.conn_trans m (G.conn_adj m hyz) (G.open_box_conn m hUg heo
    (C.seed_contains_entry r hw hz) (Box.center_mem_cube _ _))

end LatticeGraph
end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def replace (J : Finset E) (ξ ω : E → Bool) : E → Bool :=
  fun e => if e ∈ J then ξ e else ω e

noncomputable def fixedParameter (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) : E → Set.Icc (0 : ℝ) 1 :=
  fun e => if e ∈ J then if ξ e = true then 1 else 0 else p e

def pattern (J : Finset E) (ξ : E → Bool) : Set (E → Bool) :=
  {ω | ∀ e ∈ J, ω e = ξ e}

omit [Countable E] in
theorem measurable_replace (J : Finset E) (ξ : E → Bool) : Measurable (replace J ξ) := by
  apply measurable_pi_lambda
  intro e
  by_cases he : e ∈ J
  · simp only [replace, ite_eq_left he]; exact measurable_const
  · simp only [replace, ite_eq_right he]; exact measurable_pi_apply e

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

omit [Countable E] in
theorem map_replace (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have h (e : E) :
      (bernoulliMeasure true false (p e)).map (fun b : Bool => if e ∈ J then ξ e else b) =
        bernoulliMeasure true false (fixedParameter p J ξ e) := by
    by_cases he : e ∈ J
    · simp only [he,ite_true,fixedParameter]
      cases ξ e <;> simp
    · simp only [he,ite_false,fixedParameter]
      exact Measure.map_id
  change (Measure.infinitePi (fun e => bernoulliMeasure true false (p e))).map
    (fun ω e => (fun b => if e ∈ J then ξ e else b) (ω e)) = _
  rw [Measure.infinitePi_map_pi]
  · simp only [h,ProductCylinder.law]
  · intro e; exact measurable_of_countable _

private abbrev bitSigma (e : E) : MeasurableSpace (E → Bool) :=
  MeasurableSpace.comap (fun ω => ω e) inferInstance

omit [Countable E] in
private theorem measurable_replace_compl (J : Finset E) (ξ : E → Bool) :
    @Measurable (E → Bool) (E → Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e)
      inferInstance (replace J ξ) := by
  apply @measurable_pi_lambda (E → Bool) E (fun _ => Bool) (⨆ e ∈ (J : Set E)ᶜ, bitSigma e) _ (replace J ξ)
  intro e
  by_cases he : e ∈ J
  · simp only [replace,ite_eq_left he]; exact measurable_const
  · simp only [replace,ite_eq_right he]
    exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

private theorem measurable_pattern_sigma (J : Finset E) (ξ : E → Bool) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] (pattern J ξ) := by
  simp only [pattern,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro e
  apply MeasurableSet.iInter
  intro he
  apply measurableSet_eq_fun _ measurable_const
  exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))

/-- Literal finite-history factorization, including impossible histories. -/
theorem pattern_inter (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint
    (fun e => (measurable_pi_apply e).comap_le) hmi
    (disjoint_compl_right (α := Set E) (a := (J : Set E)))
  have hh := (h.indepSet_of_measurableSet (measurable_pattern_sigma J ξ)
    ((measurable_replace_compl J ξ) hA)).measure_inter_eq_mul
  have heq : pattern J ξ ∩ replace J ξ ⁻¹' A = pattern J ξ ∩ A := by
    ext ω
    constructor <;> rintro ⟨hp,ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
    · exact ⟨hp,by simpa only [Set.mem_preimage,replace_eq_of_pattern hp] using ha⟩
  rw [heq] at hh
  rw [←map_replace p J ξ,Measure.map_apply (measurable_replace J ξ) hA]
  exact hh

theorem pattern_inter_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    (ProductCylinder.law p).real (pattern J ξ ∩ A) =
      (ProductCylinder.law p).real (pattern J ξ) *
        (ProductCylinder.law (fixedParameter p J ξ)).real A := by
  simp only [Measure.real_def,pattern_inter p J ξ A hA,ENNReal.toReal_mul]

omit [Countable E] in
theorem pattern_extend_iff (J : Finset E) (a : J → Bool) (ω : E → Bool) :
    ω ∈ pattern J (ProductCylinder.extend J a) ↔ J.restrict ω = a := by
  constructor
  · intro h; funext e
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left e.2] using h e e.2
  · intro h e he
    have hh := congrFun h ⟨e,he⟩
    simpa only [Finset.restrict,ProductCylinder.extend,dite_eq_left he] using hh

/-- Partition a finite reveal without conditioning on any unrevealed event. -/
theorem measure_select (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} =
      ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) *
        (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a) := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq,measureReal_iUnion_fintype]
  · exact Finset.sum_congr rfl (fun a _ => pattern_inter_real p J _ _ (hA a))
  · intro a b hab
    apply Set.disjoint_left.mpr
    intro ω ha hb
    exact hab (((pattern_extend_iff J a ω).mp ha.1).symm.trans
      ((pattern_extend_iff J b ω).mp hb.1))
  · intro a; exact (measurableSet_pattern _ _).inter (hA a)

theorem sum_pattern_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) :
    ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) = 1 := by
  simpa only [Set.mem_univ,Set.ofPred_true,probReal_univ,mul_one] using
    (measure_select p J (fun _ => Set.univ) (fun _ => MeasurableSet.univ)).symm

omit [Countable E] in
theorem fixedParameter_congr (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    {ξ ξ' : E → Bool} (h : ∀ e ∈ J, ξ e = ξ' e) :
    fixedParameter p J ξ = fixedParameter p J ξ' := by
  funext e
  by_cases he : e ∈ J
  · simp only [fixedParameter,he,ite_true,h e he]
  · simp only [fixedParameter,he,ite_false]

theorem measurableSet_select (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    MeasurableSet {ω | ω ∈ A (J.restrict ω)} := by
  have heq : {ω | ω ∈ A (J.restrict ω)} =
      ⋃ a : J → Bool, pattern J (ProductCylinder.extend J a) ∩ A a := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,pattern_extend_iff]
    exact ⟨fun h => ⟨J.restrict ω,rfl,h⟩, fun ⟨a,ha,h⟩ => ha.symm ▸ h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (measurableSet_pattern _ _).inter (hA a))

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

private theorem measurable_determined_sigma (J : Finset E) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] A := by
  let M := ⨆ e ∈ (J : Set E), bitSigma e
  let mask : (E → Bool) → (E → Bool) := fun ω e => if e ∈ J then ω e else false
  have hm : @Measurable (E → Bool) (E → Bool) M MeasurableSpace.pi mask := by
    apply @measurable_pi_lambda (E → Bool) E (fun _ => Bool) M _ mask
    intro e
    by_cases he : e ∈ J
    · simp only [mask,ite_eq_left he]
      exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
    · simp only [mask,ite_eq_right he]; exact measurable_const
  have heq : mask ⁻¹' A = A := by
    ext ω
    exact eq_iff_iff.mp (hA ω (mask ω) (fun e he => by simp [mask,he]))
  rw [←heq]
  exact hm (ProductCylinder.measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h)))

/-- Arbitrary observables of disjoint finite blocks are independent under the
infinite product law, also when other coordinates have been fixed to 0 or 1. -/
theorem indepSet_determined (p : E → Set.Icc (0 : ℝ) 1) (J K : Finset E)
    (hJK : Disjoint J K) (A B : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ B)) :
    IndepSet A B (ProductCylinder.law p) := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le) hmi
    (show Disjoint (J : Set E) (K : Set E) from Finset.disjoint_coe.mpr hJK)
  exact h.indepSet_of_measurableSet (measurable_determined_sigma J A hA)
    (measurable_determined_sigma K B hB)

theorem disjoint_blocks_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J : I → Finset E) (hJ : Pairwise (fun i j => Disjoint (J i) (J j)))
    (A : I → Set (E → Bool))
    (hA : ∀ i, ProductCylinder.DeterminedBy (F := Prop) (J i) (fun ω => ω ∈ A i))
    (s : Finset I) :
    (ProductCylinder.law p).real {ω | ∀ i ∈ s, ω ∈ A i} =
      ∏ i ∈ s, (ProductCylinder.law p).real (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,false_implies,implies_true,Set.ofPred_true,
      probReal_univ,Finset.prod_empty]
  | @insert i s hi ih =>
    have hdis : Disjoint (J i) (s.biUnion J) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp he'
      exact Finset.disjoint_left.mp (hJ (ne_of_mem_of_not_mem hj hi).symm) he hej
    have hdet : ProductCylinder.DeterminedBy (F := Prop) (s.biUnion J)
        (fun ω => ∀ j ∈ s, ω ∈ A j) := by
      intro ω ω' h
      apply propext
      constructor <;> intro hh j hj
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mp (hh j hj)
      · exact (eq_iff_iff.mp (hA j ω ω' (fun e he => h e (Finset.mem_biUnion.mpr ⟨j,hj,he⟩)))).mpr (hh j hj)
    have hh := (indepSet_determined p (J i) (s.biUnion J) hdis (A i)
      {ω | ∀ j ∈ s, ω ∈ A j} (hA i) hdet).measure_inter_eq_mul
    have heq : {ω | ∀ j ∈ insert i s, ω ∈ A j} = A i ∩ {ω | ∀ j ∈ s, ω ∈ A j} := by
      ext ω; simp only [Finset.mem_insert,forall_eq_or_imp,Set.mem_ofPred_eq,Set.mem_inter_iff]
    rw [heq,Measure.real_def,hh,ENNReal.toReal_mul]
    change (ProductCylinder.law p).real (A i) *
      (ProductCylinder.law p).real {ω | ∀ j ∈ s, ω ∈ A j} = _
    rw [ih,Finset.prod_insert hi]

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

noncomputable def bitProbability (p : Set.Icc (0 : ℝ) 1) (b : Bool) : ℝ :=
  if b then p else 1-(p : ℝ)

theorem single_probability (p : E → Set.Icc (0 : ℝ) 1) (e : E) (b : Bool) :
    (ProductCylinder.law p).real {ω | ω e = b} = bitProbability (p e) b := by
  have h := Measure.infinitePi_map_eval (fun e : E => bernoulliMeasure true false (p e)) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = b} = (fun ω => ω e) ⁻¹' {b} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun e : E => bernoulliMeasure true false (p e))).map
    (fun ω => ω e) {b}).toReal = _
  rw [h]
  change (bernoulliMeasure true false (p e)).real {b} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases b <;> simp [bitProbability,unitInterval.coe_symm_eq]

theorem finite_pattern_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (ξ : E → Bool) :
    (ProductCylinder.law p).real (pattern J ξ) = ∏ e ∈ J, bitProbability (p e) (ξ e) := by
  classical
  have hd : Pairwise (fun e f : E => Disjoint ({e} : Finset E) {f}) := by
    intro e f h; simpa using h
  have hdet (e : E) : ProductCylinder.DeterminedBy (F := Prop) {e}
      (fun ω : E → Bool => ω e = ξ e) := by
    intro ω ω' h
    dsimp only
    rw [h e (Finset.mem_singleton_self e)]
  have h := disjoint_blocks_probability p (fun e : E => {e}) hd
    (fun e => {ω | ω e = ξ e}) hdet J
  simpa only [pattern,Set.mem_ofPred_eq,single_probability] using h

def allValue (J : Finset E) (b : Bool) : Set (E → Bool) := {ω | ∀ e ∈ J, ω e = b}

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_allValue (J : Finset E) (b : Bool) : MeasurableSet (allValue J b) :=
  ProductCylinder.measurableSet_determined J _
    (fun ω ω' h => eq_iff_iff.mp (allValue_determined J b ω ω' h))

theorem allValue_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = ∏ e ∈ J, bitProbability (p e) b :=
  finite_pattern_probability p J (fun _ => b)

theorem allValue_probability_constant (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (q : Set.Icc (0 : ℝ) 1) (hp : ∀ e ∈ J, p e = q) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = (bitProbability q b)^J.card := by
  rw [allValue_probability]
  calc
    _ = ∏ _e ∈ J, bitProbability q b := Finset.prod_congr rfl (fun e he => by rw [hp e he])
    _ = _ := by rw [Finset.prod_const]

/-- A reveal has no effect on any observable determined by disjoint bits. -/
theorem fixed_determined_probability (p : E → Set.Icc (0 : ℝ) 1)
    (J K : Finset E) (hJK : Disjoint J K) (ξ : E → Bool) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ A)) :
    (ProductCylinder.law (fixedParameter p J ξ)).real A = (ProductCylinder.law p).real A := by
  have hAm := ProductCylinder.measurableSet_determined K A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  rw [←map_replace,Measure.real_def,Measure.map_apply (measurable_replace _ _) hAm]
  have heq : replace J ξ ⁻¹' A = A := by
    ext ω
    apply eq_iff_iff.mp (hA ω (replace J ξ ω) ?_)
    intro e he
    apply ite_eq_right
    exact fun heJ => Finset.disjoint_left.mp hJK heJ he
  rw [heq]
  rfl

variable [Countable E]

theorem ae_fixed_pattern (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), ω ∈ pattern J ξ := by
  rw [←map_replace]
  apply (ae_map_iff (measurable_replace J ξ).aemeasurable
    (measurableSet_pattern J ξ)).mpr
  exact Filter.Eventually.of_forall (fun ω e he => ite_eq_left he)

/-- On a fixed revealed pattern, every J-determined quantity is constant. -/
theorem ae_fixed_determined {F : Sort uF} (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) (f : (E → Bool) → F)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), f ω = f ξ := by
  filter_upwards [ae_fixed_pattern p J ξ] with ω hω
  exact hf ξ ω hω

end InfiniteConditioning

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem select_probability_le (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real
      (A a) ≤ b) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} ≤ b := by
  rw [measure_select p J A hA]
  calc
    _ ≤ ∑ a : J → Bool, (ProductCylinder.law p).real
        (pattern J (ProductCylinder.extend J a)) * b :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hb a) measureReal_nonneg)
    _ = b := by rw [←Finset.sum_mul,sum_pattern_real,one_mul]

/-- Exact lower bound after a selected reveal; null histories are included. -/
theorem select_probability_lower (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (P : (J → Bool) → Prop) (A : (J → Bool) → Set (E → Bool))
    (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, P a → b ≤
      (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a)) :
    b * (ProductCylinder.law p).real {ω | P (J.restrict ω)} ≤
      (ProductCylinder.law p).real {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} := by
  classical
  let B : (J → Bool) → Set (E → Bool) := fun a => if P a then Set.univ else ∅
  let C : (J → Bool) → Set (E → Bool) := fun a => if P a then A a else ∅
  have hPm : {ω | P (J.restrict ω)} = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [B,h]
  have hAm : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
      {ω | ω ∈ C (J.restrict ω)} := by
    ext ω; by_cases h : P (J.restrict ω) <;> simp [C,h]
  have hB (a) : MeasurableSet (B a) := by dsimp [B]; split_ifs <;> measurability
  have hC (a) : MeasurableSet (C a) := by dsimp [C]; split_ifs; exact hA a; exact MeasurableSet.empty
  rw [hPm,hAm,measure_select p J B hB,measure_select p J C hC,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P a
  · simp only [B,C,ha,ite_true,probReal_univ,mul_one]
    calc
      _ = (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a))*b := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb a ha) measureReal_nonneg
  · simp only [B,C,ha,ite_false,measureReal_empty,mul_zero]
    exact le_rfl

end InfiniteConditioning

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

noncomputable def conditionalProbability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (ξ : E → Bool) : ℝ :=
  (ProductCylinder.law (fixedParameter p J ξ)).real C

omit [Countable E] in
theorem conditionalProbability_determined (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) :
    ProductCylinder.DeterminedBy J (conditionalProbability p J C) := by
  intro ω ω' h
  unfold conditionalProbability
  rw [fixedParameter_congr p J h]

/-- Reveal-wise tower/Markov bound, valid also for histories of zero mass. -/
theorem conditional_failure_mass (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} (_hδ : 0 ≤ δ) :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set (E → Bool) :=
    if ξ a ∈ H ∧ conditionalProbability p J C (ξ a) ≤ 1-δ then Set.univ else ∅
  let B (a : J → Bool) : Set (E → Bool) := if ξ a ∈ H then Cᶜ else ∅
  have hA (a) : MeasurableSet (A a) := by dsimp only [A]; split_ifs <;> measurability
  have hB (a) : MeasurableSet (B a) := by
    dsimp only [B]; split_ifs
    · exact hC.compl
    · exact MeasurableSet.empty
  have heA : {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    have hc := ProductCylinder.determinedBy_eq_extend (conditionalProbability_determined p J C) ω
    change conditionalProbability p J C ω = conditionalProbability p J C (ξ (J.restrict ω)) at hc
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_ofPred_eq,A,hh,hc]
    split_ifs <;> simp_all
  have heB : H ∩ Cᶜ = {ω | ω ∈ B (J.restrict ω)} := by
    ext ω
    have hh := ProductCylinder.determinedBy_eq_extend hH ω
    change (ω ∈ H) = (ξ (J.restrict ω) ∈ H) at hh
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,B,hh]
    split_ifs <;> simp_all
  rw [heA,heB,measure_select p J A hA,measure_select p J B hB,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have hcomp : (ProductCylinder.law (fixedParameter p J (ξ a))).real Cᶜ =
      1-conditionalProbability p J C (ξ a) := by
    simpa only [conditionalProbability,probReal_univ] using
      (measureReal_compl (μ := ProductCylinder.law (fixedParameter p J (ξ a))) hC)
  have hlocal : δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a) ≤
      (ProductCylinder.law (fixedParameter p J (ξ a))).real (B a) := by
    by_cases hha : ξ a ∈ H
    · simp only [A,B,hha,true_and,ite_true]
      split_ifs with hc
      · rw [probReal_univ,mul_one,hcomp]; linarith
      · rw [measureReal_empty,mul_zero]; exact measureReal_nonneg
    · simp only [A,B,hha,false_and,ite_false,measureReal_empty,mul_zero,le_refl]
  let hw := (ProductCylinder.law p).real (pattern J (ξ a))
  calc
    _ = hw*(δ*(ProductCylinder.law (fixedParameter p J (ξ a))).real (A a)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlocal measureReal_nonneg

theorem conditional_failure_bound (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ ε : ℝ} (hδ : 0 < δ)
    (hfail : (ProductCylinder.law p).real (H ∩ Cᶜ) ≤ ε) :
    (ProductCylinder.law p).real {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤ ε/δ := by
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using (conditional_failure_mass p J H C hH hC hδ.le).trans hfail

end InfiniteConditioning

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open MeasureTheory ProbabilityTheory Classical
namespace ShellEstimates
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Averaging disjoint blocking events supplies a deterministic shell layer. -/
theorem exists_layer {I : Type uI} [Fintype I] [Nonempty I]
    (Q A : I → Set Ω) (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j))) {α : ℝ} (hα : 0 < α)
    (hblock : ∀ i, α*μ.real (Q i) ≤ μ.real (A i)) :
    ∃ i, μ.real (Q i) ≤ 1/(α*Fintype.card I) := by
  have hs : ∑ i, μ.real (A i) ≤ 1 := by
    rw [←measureReal_iUnion_fintype hAd hAm]
    exact measureReal_le_one
  have hsQ : α*(∑ i, μ.real (Q i)) ≤ 1 := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum (fun i _ => hblock i)).trans hs
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  by_contra! hnone
  have ht : (∑ _i : I, 1/(α*Fintype.card I)) < ∑ i, μ.real (Q i) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hnone i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  have he : (Fintype.card I : ℝ)*(1/(α*Fintype.card I)) = 1/α := by field_simp
  rw [he] at ht
  have hh := (div_lt_iff₀ hα).mp ht
  nlinarith

theorem success_count_bound (S : Ω → ℝ) (hS : MemLp S 2 μ)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ ω, S ω ∂μ = a)
    (hvar : variance S μ ≤ a) :
    μ.real {ω | S ω < a/2} ≤ 4/a := by
  have hcheb := meas_ge_le_variance_div_sq hS (show 0 < a/2 by positivity)
  rw [hmean] at hcheb
  have hs : {ω | S ω < a/2} ⊆ {ω | a/2 ≤ |S ω-a|} := by
    intro ω hω
    have hh : a/2 ≤ a-S ω := by dsimp at hω ⊢; linarith
    exact hh.trans (le_abs_self _ |>.trans_eq (abs_sub_comm a (S ω)))
  have hle : μ {ω | S ω < a/2} ≤ ENNReal.ofReal (variance S μ/(a/2)^2) :=
    (measure_mono hs).trans hcheb
  have hv0 : 0 ≤ variance S μ/(a/2)^2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hr : μ.real {ω | S ω < a/2} ≤ variance S μ/(a/2)^2 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hle |>.trans_eq
      (ENNReal.toReal_ofReal hv0)
  apply hr.trans
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < a/2 by positivity))).mpr
  have he : (4/a)*(a/2)^2 = a := by field_simp; ring
  rwa [he]

/- Bad successes only need a first moment; no mutual independence is used. -/
omit [IsProbabilityMeasure μ] in
theorem bad_count_bound (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {a γ τ : ℝ} (ha : 0 < a) (_hτ : 0 < τ)
    (hmean : ∫ ω, Z ω ∂μ ≤ a*γ/τ) :
    μ.real {ω | a/2 ≤ Z ω} ≤ 2*γ/τ := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hZ0) hZ (a/2)
  have hm : (a/2)*μ.real {ω | a/2 ≤ Z ω} ≤ a*γ/τ := h.trans hmean
  have he : (a/2)*(2*γ/τ) = a*γ/τ := by ring
  rw [←he] at hm
  exact (mul_le_mul_iff_right₀ (show 0 < a/2 by positivity)).mp hm

/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
omit [MeasurableSpace Ω] in
theorem no_good_subset (S Z : Ω → ℝ) (G : Set Ω) (a : ℝ)
    (h : ∀ ω, ω ∉ G → S ω ≤ Z ω) :
    Gᶜ ⊆ {ω | S ω < a/2} ∪ {ω | a/2 ≤ Z ω} := by
  intro ω hω
  by_cases hs : S ω < a/2
  · exact Or.inl hs
  · exact Or.inr (le_trans (le_of_not_gt hs) (h ω hω))

end ShellEstimates

namespace TrialCounts
open MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def count (A : I → Set Ω) : Ω → ℝ :=
  fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω

theorem count_memLp (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (count A) 2 μ := by
  apply memLp_finsetSum
  intro i _
  exact (memLp_const (1 : ℝ)).indicator (hA i)

omit [MeasurableSpace Ω] in
theorem count_nonneg (A : I → Set Ω) (ω : Ω) : 0 ≤ count A ω := by
  apply Finset.sum_nonneg
  intro i _
  by_cases h : ω ∈ A i <;> simp [Set.indicator,h]

omit [IsProbabilityMeasure μ] in
theorem indicator_mean (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real A :=
  integral_indicator_one hA

theorem count_mean (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    (∫ ω, count A ω ∂μ) = ∑ i, μ.real (A i) := by
  unfold count
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_one (hA i)
  · intro i _
    exact ((memLp_const (1 : ℝ)).indicator (hA i)).integrable (by norm_num : (1 : ENNReal) ≤ 2)

omit [MeasurableSpace Ω] in
theorem indicator_product (A B : Set Ω) :
    A.indicator (fun _ => (1 : ℝ)) * B.indicator (fun _ => (1 : ℝ)) =
      (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [Set.indicator,hA,hB]

/-- Pairwise independence is all that the success-count step needs. -/
theorem count_variance_le (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c) :
    variance (count A) μ ≤ Fintype.card I*c := by
  let X (i : I) : Ω → ℝ := (A i).indicator (fun _ => (1 : ℝ))
  have hX (i : I) : MemLp (X i) 2 μ := (memLp_const (1 : ℝ)).indicator (hA i)
  have hcov (i j : I) : covariance (X i) (X j) μ ≤ if i = j then c else 0 := by
    have hprod : X i * X j = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) :=
      indicator_product (A i) (A j)
    rw [covariance_eq_sub (hX i) (hX j),hprod,
      indicator_mean μ _ ((hA i).inter (hA j))]
    change μ.real (A i ∩ A j) -
      (∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ)*
      (∫ ω, (A j).indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤ _
    rw [indicator_mean μ _ (hA i),indicator_mean μ _ (hA j),hc i,hc j]
    by_cases hij : i = j
    · subst j
      simp only [ite_true,Set.inter_self,hc]
      nlinarith [sq_nonneg c]
    · simp only [hij,ite_false]
      linarith [hpair i j hij]
  have he : count A = ∑ i, X i := by ext ω; simp [count,X]
  rw [he,variance_sum hX]
  calc
    _ ≤ ∑ i : I, ∑ j : I, if i = j then c else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = Fintype.card I*c := by simp

/-- No independence is required among bad successes or their quality tests. -/
theorem no_good_probability (A B : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    {c γ τ : ℝ} (hcpos : 0 < Fintype.card I*c) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c)
    (hbad : ∀ i, μ.real (B i) ≤ c*γ/τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4/(Fintype.card I*c)+2*γ/τ := by
  let a : ℝ := Fintype.card I*c
  have hm : (∫ ω, count A ω ∂μ) = a := by
    rw [count_mean μ A hA]
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]
  have hs := ShellEstimates.success_count_bound μ (count A) (count_memLp μ A hA)
    hcpos hm (count_variance_le μ A hA hc hpair)
  have hbmean : (∫ ω, count B ω ∂μ) ≤ a*γ/τ := by
    rw [count_mean μ B hB]
    calc
      _ ≤ ∑ _i : I, c*γ/τ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = a*γ/τ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]; ring
  have hb := ShellEstimates.bad_count_bound μ (count B)
    ((count_memLp μ B hB).integrable (by norm_num)) (count_nonneg B) hcpos hτ hbmean
  have hsub : {ω | ∀ i, ω ∈ A i → ω ∈ B i} ⊆
      {ω | count A ω < a/2} ∪ {ω | a/2 ≤ count B ω} := by
    intro ω hω
    by_cases hs : count A ω < a/2
    · exact Or.inl hs
    · apply Or.inr
      apply (le_of_not_gt hs).trans
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ω ∈ A i
      · simp [Set.indicator,hi,hω i hi]
      · simp only [Set.indicator,hi,ite_false]
        split_ifs <;> norm_num
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hs hb))

end TrialCounts

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem shell_blocking_lower (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L : ℕ)
    (hp : ∀ y, C.Exterior y → p (C.entryBit m y) = q) :
    (1-p₀)^L * (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} ≤
    (ProductCylinder.law p).real
      {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
        G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let P (a : J → Bool) := 0 < (G.entrants m C (ξ a) o).card ∧
    (G.entrants m C (ξ a) o).card < L
  let A (a : J → Bool) := allValue (G.entryBits m C (ξ a) o) false
  have h := select_probability_lower p J P A (fun a => measurableSet_allValue _ _) (b := (1-p₀)^L) ?_
  · have hY (ω : m.Config) : G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK (ω : m.Config) : G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o :=
      ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    have heP : {ω | P (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L} := by
      ext ω; simp only [P,Set.mem_ofPred_eq]; rw [←hY ω]
    have heA : {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} =
        {ω | 0 < (G.entrants m C ω o).card ∧ (G.entrants m C ω o).card < L ∧
          G.Blocked m C ω o} := by
      ext ω
      simp only [P,A,allValue,Blocked,Set.mem_ofPred_eq]
      rw [←hY ω,←hK ω]
      exact and_assoc
    rwa [heP,heA] at h
  · intro a ha
    rw [fixed_determined_probability p J (G.entryBits m C (ξ a) o)
      (G.entryBits_disjoint_outside m C (ξ a) o).symm _ _ (allValue_determined _ _)]
    rw [allValue_probability_constant p _ q ?_ false]
    · change (1-p₀)^L ≤ (1-(q : ℝ))^(G.entryBits m C (ξ a) o).card
      have h0 : 0 ≤ 1-p₀ := by linarith
      have h1 : 1-(q : ℝ) ≤ 1 := by linarith [q.property.1]
      calc
        _ ≤ (1-(q : ℝ))^L := pow_le_pow_left₀ h0 (by linarith) L
        _ ≤ _ := pow_le_pow_of_le_one (by linarith [q.property.2]) h1
          ((G.entryBits_card m C (ξ a) o).trans (Nat.le_of_lt ha.2))
    · intro e he
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      have hyG : y ∈ G.vertices := (Finset.mem_filter.mp hy).1
      exact hp y ((G.mem_entrants m C (ξ a) o ⟨y,hyG⟩).mp hy).1

theorem measurableSet_shell_blocked (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
  let J := G.outsideBits m C
  let ξ (a : J → Bool) := ProductCylinder.extend J a
  let A (a : J → Bool) : Set m.Config := if 0 < (G.entrants m C (ξ a) o).card ∧
      (G.entrants m C (ξ a) o).card < L then allValue (G.entryBits m C (ξ a) o) false else ∅
  have h := measurableSet_select J A (fun a => by
    dsimp only [A]; split_ifs
    · exact measurableSet_allValue _ _
    · exact MeasurableSet.empty)
  have he : {ω | ω ∈ A (J.restrict ω)} = {ω | 0 < (G.entrants m C ω o).card ∧
      (G.entrants m C ω o).card < L ∧ G.Blocked m C ω o} := by
    ext ω
    have hY := ProductCylinder.determinedBy_eq_extend (G.entrants_determined m C o) ω
    have hK := ProductCylinder.determinedBy_eq_extend (G.entryBits_determined m C o) ω
    change G.entrants m C ω o = G.entrants m C (ξ (J.restrict ω)) o at hY
    change G.entryBits m C ω o = G.entryBits m C (ξ (J.restrict ω)) o at hK
    simp only [A,←hY,←hK,Set.mem_ofPred_eq,Blocked,allValue]
    split_ifs with hh
    · tauto
    · simp only [Set.mem_empty_iff_false]; tauto
  rwa [he] at h

/-- Deterministic shell selection for the finite graph in bond and site percolation. -/
theorem exists_shell (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (B : Box) (o : G.Node) (q : Set.Icc (0 : ℝ) 1) {p₀ : ℝ}
    (hq : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1) (L a R : ℕ) (haR : a < R)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ j ∈ Finset.Ico a R, ∀ y, (B.expand j).Exterior y →
      p ((B.expand j).entryBit m y) = q) :
    ∃ j ∈ Finset.Ico a R, (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand j) ω o).card < L} ≤
      1/((1-p₀)^L*(R-a : ℕ)) := by
  let I := ↥(Finset.Ico a R)
  have : Nonempty I := ⟨⟨a,Finset.mem_Ico.mpr ⟨le_rfl,haR⟩⟩⟩
  let Q (i : I) : Set m.Config :=
    {ω | G.Meets m ω o {x | B.Contains x} ∧ (G.entrants m (B.expand i.1) ω o).card < L}
  let A (i : I) : Set m.Config :=
    {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
      (G.entrants m (B.expand i.1) ω o).card < L ∧ G.Blocked m (B.expand i.1) ω o}
  have hoi (i : I) : ¬(B.expand i.1).Contains o.1 := fun h =>
    ho (B.expand_mono (Nat.le_of_lt (Finset.mem_Ico.mp i.2).2) h)
  have hAd : Pairwise (fun i j : I => Disjoint (A i) (A j)) := by
    intro i j hij
    have hi : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    apply Set.disjoint_left.mpr
    intro ω hωi hωj
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have he := G.blocked_earlier_entrants m hlt (hoi j) hωj.2.2
      have hpos := hωi.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
    · have he := G.blocked_earlier_entrants m hlt (hoi i) hωi.2.2
      have hpos := hωj.1
      rw [he,Finset.card_empty] at hpos
      exact Nat.not_lt_zero _ hpos
  have hblock (i : I) : (1-p₀)^L * (ProductCylinder.law p).real (Q i) ≤
      (ProductCylinder.law p).real (A i) := by
    have hsub : Q i ⊆ {ω | 0 < (G.entrants m (B.expand i.1) ω o).card ∧
        (G.entrants m (B.expand i.1) ω o).card < L} := by
      intro ω hω
      refine ⟨Finset.card_pos.mpr (G.meets_entrants_nonempty m (hoi i) ?_),hω.2⟩
      obtain ⟨z,hz,hconn⟩ := hω.1
      exact ⟨z,B.contains_expand i.1 hz,hconn⟩
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg (by linarith) _)).trans
      (G.shell_blocking_lower m p (B.expand i.1) o q hq hp₀ L (hp i.1 i.2))
  obtain ⟨i,hi⟩ := ShellEstimates.exists_layer (ProductCylinder.law p) Q A
    (fun i => G.measurableSet_shell_blocked m (B.expand i.1) o L) hAd
    (pow_pos (by linarith) L) hblock
  refine ⟨i.1,i.2,?_⟩
  simpa only [I,Fintype.card_coe,Nat.card_Ico] using hi

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

theorem indicator_monotone {P : (E → Bool) → Prop} (hP : Monotone P) :
    Monotone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and_increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Monotone P) (hQ : Monotone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := increasing p _ _ (indicator_monotone hP) (indicator_monotone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]
end FiniteAssociation

namespace ProductCylinder
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem probability_congr_parameters (J : Finset E)
    (p q : E → Set.Icc (0 : ℝ) 1) (hpq : ∀ e ∈ J, p e = q e)
    (A : Set (E → Bool)) (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    (law p).real A = (law q).real A := by
  simp only [Measure.real_def,probability_determined J _ A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))]
  congr 2
  unfold finiteLaw
  congr 1
  funext e
  rw [hpq e e.2]

theorem determinedBy_mono {J K : Finset E} (hJK : J ⊆ K) {F : Type}
    {f : (E → Bool) → F} (hf : DeterminedBy J f) : DeterminedBy K f :=
  fun ω ω' h => hf ω ω' (fun e he => h e (hJK he))

theorem increasing_and (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A B : Set (E → Bool))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : DeterminedBy (F := Prop) J (fun ω => ω ∈ B))
    (hmA : Monotone (fun ω => ω ∈ A)) (hmB : Monotone (fun ω => ω ∈ B)) :
    (law p).real A*(law p).real B ≤ (law p).real (A ∩ B) := by
  have he (C : Set (E → Bool)) (hC : DeterminedBy (F := Prop) J (fun ω => ω ∈ C)) :
      (law p).real C = FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ C) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p C (fun ω ω' h => eq_iff_iff.mp (hC ω ω' h))]
    rfl
  have hAB : DeterminedBy (F := Prop) J (fun ω => ω ∈ A ∩ B) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,hA ω ω' h,hB ω ω' h]
  rw [he A hA,he B hB,he (A ∩ B) hAB]
  exact FiniteAssociation.prob_and_increasing _ (hmA.comp (extend_mono J)) (hmB.comp (extend_mono J))

/-- The open-seed Harris estimate, with a separate increasing connecting event. -/
theorem seed_failure_bound (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (O A C : Set (E → Bool))
    (hO : DeterminedBy (F := Prop) J (fun ω => ω ∈ O))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hmO : Monotone (fun ω => ω ∈ O)) (hmA : Monotone (fun ω => ω ∈ A))
    (hsub : O ∩ A ⊆ C) {γ : ℝ} (hprob : 1-γ ≤ (law p).real A) :
    (law p).real (O ∩ Cᶜ) ≤ (law p).real O*γ := by
  have hm := measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  have ha := increasing_and J p O A hO hA hmO hmA
  have hadd := measureReal_inter_add_sdiff (μ := law p) (s := O) hm
  have hsub' : O ∩ Cᶜ ⊆ O \ A := by
    intro ω hω
    exact ⟨hω.1,fun h => hω.2 (hsub ⟨hω.1,h⟩)⟩
  have hle := measureReal_mono (μ := law p) hsub'
  have h0 : 0 ≤ (law p).real O := measureReal_nonneg
  nlinarith
end ProductCylinder

namespace InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem allValue_true_monotone (J : Finset E) : Monotone (fun ω => ω ∈ allValue J true) := by
  intro ω ω' h hh e he
  have hi := h e
  rw [hh e he] at hi
  exact le_antisymm le_top hi

theorem measurableSet_conditional_test (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (a : ℝ) :
    MeasurableSet {ω | conditionalProbability p J C ω ≤ a} := by
  refine ProductCylinder.measurableSet_determined J _ ?_
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,conditionalProbability_determined p J C ω ω' h]
end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem conn_mono {ω ω' : m.Config} (h : ω ≤ ω') {x y : G.Node}
    (hc : G.Conn m ω x y) : G.Conn m ω' x y := by
  have hopen {e : m.Bit} (he : ω e = true) : ω' e = true := by
    have hi := h e
    rw [he] at hi
    exact le_antisymm le_top hi
  obtain ⟨hx,hc⟩ := (G.conn_iff m ω x y).mp hc
  refine (G.conn_iff m ω' x y).mpr ⟨?_,?_⟩
  · cases m
    · trivial
    · exact hopen hx
  · apply Relation.ReflTransGen.mono (r := G.Adj m ω) (p := G.Adj m ω') ?_ x y hc
    intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,he,hi,hopen ho⟩
    · exact ⟨hab.1,hopen hab.2.1,hopen hab.2.2⟩

theorem meets_mono (o : G.Node) (T : Set Vertex) : Monotone (fun ω => G.Meets m ω o T) := by
  intro ω ω' h ⟨y,hy,hc⟩
  exact ⟨y,hy,G.conn_mono m h hc⟩

noncomputable def goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) (ω : m.Config) : Set Vertex :=
  {v | ∃ a : G.Node, a.1 = v ∧ 1-τ < conditionalProbability p J {ω | G.Meets m ω a T} ω}

theorem goodRelays_determined (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) : ProductCylinder.DeterminedBy J (G.goodRelays m p J T τ) := by
  intro ω ω' h
  ext v
  simp only [goodRelays,Set.mem_ofPred_eq,conditionalProbability_determined p J _ ω ω' h]

theorem random_relay_failure (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} ≤ τ := by
  let A (a : J → Bool) : Set m.Config :=
    {ω | G.Meets m ω o (G.goodRelays m p J T τ (ProductCylinder.extend J a)) ∧ ¬G.Meets m ω o T}
  have he : {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    simp only [A,Set.mem_ofPred_eq,
      ProductCylinder.determinedBy_eq_extend (G.goodRelays_determined m p J T τ) ω]
  rw [he]
  apply select_probability_le p J A
  · intro a
    exact (G.measurableSet_meets m _ _).inter (G.measurableSet_meets m _ _).compl
  · intro a
    apply G.failure_comparison m _ o _ T hτ
    intro v ⟨u,hu,hh⟩
    have heu : u = v := Subtype.ext hu
    subst u
    exact hh.le

end CriticalZ3.LatticeGraph

end OAI
end
end

section
section
namespace OAI

open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def BasicAdj : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω => BondOpen ω
  | .site,ω => SiteOpen ω

def VertexOpen : (m : Model) → m.Config → Vertex → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x = true

def SeedReaches (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) : Set m.Config :=
  {ω | ∃ x ∈ cube c a, m.VertexOpen ω x ∧ ∃ y ∈ T,
    Relation.ReflTransGen (Within (cube c b) (m.BasicAdj ω)) x y}

@[simp] theorem seedReaches_bond (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .bond c a b T = bondSeedReaches c a b T := by
  ext ω; simp [SeedReaches,bondSeedReaches,VertexOpen,BasicAdj]
@[simp] theorem seedReaches_site (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    SeedReaches .site c a b T = siteSeedReaches c a b T := rfl

theorem seedReaches_mono (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ m.SeedReaches c a b T) := by
  cases m
  · simpa only [seedReaches_bond] using bondSeedReaches_mono c a b T
  · exact siteSeedReaches_mono c a b T
end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

theorem cube_bonds_eq (c : Vertex) (r : ℕ) :
    (cube c r).bonds = internalBonds (CriticalZ3.cube c r) (cube_finite c r) := by
  ext e
  simp only [mem_bonds,mem_internalBonds,contains_cube_iff]

theorem cube_sites_eq (c : Vertex) (r : ℕ) :
    (cube c r).vertices = (cube_finite c r).toFinset := by
  ext e
  simp only [mem_vertices,Set.Finite.mem_toFinset,contains_cube_iff]
end Box

namespace Model

theorem seedReaches_determined (m : Model) (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) ((Box.cube c b).bits m)
      (fun ω => ω ∈ m.SeedReaches c a b T) := by
  intro ω ω' h
  apply propext
  cases m
  · rw [seedReaches_bond]
    apply bondSeedReaches_determined c a b T ω ω'
    simpa only [Box.bits,Box.cube_bonds_eq] using h
  · apply siteSeedReaches_determined c a b hab T ω ω'
    simpa only [Box.bits,Box.cube_sites_eq] using h
end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

theorem basicAdj_lift {B : Box} (hB : G.ContainsBox B) {ω : m.Config} {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : m.BasicAdj ω x.1 y.1) : G.Adj m ω x y := by
  cases m
  · rcases hxy with ⟨i,hi,ho⟩ | ⟨i,hi,ho⟩
    · have he : Incidence (x.1,i) x.1 y.1 := Or.inl ⟨rfl,hi⟩
      exact ⟨(x.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
    · have he : Incidence (y.1,i) x.1 y.1 := Or.inr ⟨rfl,hi⟩
      exact ⟨(y.1,i),hB.2 (incidence_internal hx hy he),he,ho⟩
  · obtain ⟨e,he⟩ := neighbor_incidence hxy.1
    exact ⟨⟨e,hB.2 (incidence_internal hx hy he),he⟩,hxy.2⟩

/-- Exact finite-graph continuation of the quarter-face seed event. -/
theorem seedReaches_conn {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hB : G.ContainsBox (Box.cube c b)) (T : Set Vertex) {ω : m.Config}
    {v : G.Node} (hv : v.1 = c)
    (hO : ω ∈ allValue ((Box.cube c a).bits m) true)
    (hE : ω ∈ m.SeedReaches c a b T) : G.Meets m ω v T := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  have hxy : G.Conn m ω x' y' := by
    refine (G.conn_iff m ω x' y').mpr ⟨?_,?_⟩
    · cases m <;> exact hxo
    · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
      · intro x y h
        exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
      · intro x y h
        exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
          (Box.contains_cube_iff.mpr h.2.1) h.2.2
  have hA : G.ContainsBox (Box.cube c a) := hB.mono G (fun _ h =>
    Box.contains_cube_iff.mpr (cube_mono c hab (Box.contains_cube_iff.mp h)))
  refine ⟨y',hy,G.conn_trans m ?_ hxy⟩
  apply G.open_box_conn m hA hO
  · rw [hv]; exact Box.center_mem_cube _ _
  · exact Box.contains_cube_iff.mpr hxa

theorem seed_conditional_quality (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (T : Set Vertex) {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hseed : ∀ x, (Box.cube c a).Contains x → C.Contains x)
    (hB : G.ContainsBox (Box.cube c b)) (v : G.Node) (hv : v.1 = c)
    {γ τ : ℝ} (hτ : 0 < τ)
    (hprob : 1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c a b T)) :
    (ProductCylinder.law p).real
      {ω | ω ∈ allValue ((Box.cube c a).bits m) true ∧
        conditionalProbability p (C.bits m) {ω | G.Meets m ω v T} ω ≤ 1-τ} ≤
      (ProductCylinder.law p).real (allValue ((Box.cube c a).bits m) true)*γ/τ := by
  let O := allValue ((Box.cube c a).bits m) true
  have hdet := allValue_determined ((Box.cube c a).bits m) true
  apply conditional_failure_bound p (C.bits m) O {ω | G.Meets m ω v T}
    (ProductCylinder.determinedBy_mono (Box.bits_mono m hseed) hdet)
    (G.measurableSet_meets m v T) hτ
  apply ProductCylinder.seed_failure_bound ((Box.cube c b).bits m) p O
    (m.SeedReaches c a b T) _
    (ProductCylinder.determinedBy_mono (Box.bits_mono m (fun _ h =>
      Box.contains_cube_iff.mpr (cube_mono c hab (Box.contains_cube_iff.mp h)))) hdet)
    (m.seedReaches_determined c a b hab T) (allValue_true_monotone _) (m.seedReaches_mono c a b T)
  · intro ω h
    exact G.seedReaches_conn m hab hB T hv h.1 h.2
  · exact hprob
end LatticeGraph
end CriticalZ3

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem successBits_contained (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    C.successBits r m y ⊆ (C.expand 1).bits m := by
  have hs := bits_mono m (fun x hx => C.contains_expand 1 (C.seedBox_contained r hw y x hx))
  cases m
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact LatticeGraph.incidence_internal (exterior_expand hy)
        (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
    · exact hs he
  · exact hs
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

noncomputable def relayNode (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox C) (y : Vertex) : G.Node :=
  ⟨C.relayCenter r y,G.containsBox_node hC
    (C.seedBox_contained r hw y _ (Box.center_mem_cube _ _))⟩

/-- A single bad-success mass has the extra factor q for crossing bonds. -/
theorem bad_success_mass (p : m.Bit → Set.Icc (0 : ℝ) 1) (q : Set.Icc (0 : ℝ) 1)
    (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r)
    {y : Vertex} (hy : C.Exterior y)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q)
    (F : Set m.Config) (hF : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F))
    {γ τ : ℝ} (hqual : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ F) ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real (allValue (C.successBits r m y) true ∩ F) ≤
      (q : ℝ)^Box.successCard m r*γ/τ := by
  cases m
  · have hseed := ProductCylinder.determinedBy_mono (Box.bits_mono .bond (C.seedBox_contained r hw y))
      (allValue_determined ((C.seedBox r y).bits .bond) true)
    have hd : ProductCylinder.DeterminedBy (F := Prop) C.bonds
        (fun ω => ω ∈ allValue (C.seedBox r y).bonds true ∩ F) := by
      intro ω ω' h
      change (ω' ∈ allValue ((C.seedBox r y).bits .bond) true ∧ ω' ∈ F) =
        (ω ∈ allValue ((C.seedBox r y).bits .bond) true ∧ ω ∈ F)
      exact congrArg₂ And (hseed ω ω' h) (hF ω ω' h)
    have hind := indepSet_determined p {C.entryBit .bond y} C.bonds
      (Finset.disjoint_singleton_left.mpr (C.crossing_not_internal hy))
      (allValue {C.entryBit .bond y} true) (allValue (C.seedBox r y).bonds true ∩ F)
      (allValue_determined _ _) hd
    have he : allValue (C.successBits r .bond y) true ∩ F =
        allValue {C.entryBit .bond y} true ∩ (allValue (C.seedBox r y).bonds true ∩ F) := by
      ext ω
      simp only [Box.successBits,allValue,Set.mem_inter_iff,Set.mem_ofPred_eq,
        Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
      tauto
    have hcross := hp (C.entryBit .bond y)
      (C.successBits_contained r .bond hw hy (Finset.mem_insert_self _ _))
    have hpone : (ProductCylinder.law p).real (allValue {C.entryBit .bond y} true) = (q : ℝ) := by
      rw [allValue_probability_constant p _ q (by intro e he; simpa only [Finset.mem_singleton.mp he] using hcross)]
      simp [bitProbability]
    rw [he,Measure.real_def,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
    change (ProductCylinder.law p).real (allValue {C.entryBit .bond y} true)*_ ≤ _
    rw [hpone]
    calc
      _ ≤ (q : ℝ)*((q : ℝ)^Box.seedCard .bond r*γ/τ) := mul_le_mul_of_nonneg_left hqual q.2.1
      _ = _ := by simp only [Box.successCard,pow_succ]; ring
  · simpa only [Box.successBits,Box.bits,Box.successCard,Nat.add_zero] using hqual

theorem measurableSet_meets_goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) (τ : ℝ) :
    MeasurableSet {ω | G.Meets m ω o (G.goodRelays m p J T τ ω)} := by
  refine ProductCylinder.measurableSet_determined (G.bits m ∪ J) _ ?_
  intro ω ω' h
  have hg := G.goodRelays_determined m p J T τ ω ω' (fun e he => h e (Finset.mem_union_right _ he))
  simp only [Set.mem_ofPred_eq,hg]
  exact eq_iff_iff.mp (G.meets_determined m o _ ω ω' (fun e he => h e (Finset.mem_union_left _ he)))

/-- Outside reveals preserve joint seed/quality statistics, as quality is an
interior function rather than an outside-conditional prediction. -/
theorem fixed_bad_success_mass (p : m.Bit → Set.Icc (0 : ℝ) 1) (q : Set.Icc (0 : ℝ) 1)
    (C : Box) (r : ℕ) (hw : ∀ i, C.lower i+r ≤ C.upper i-r)
    {y : Vertex} (hy : C.Exterior y) (ξ : m.Config)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q)
    (F : Set m.Config) (hF : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F))
    {γ τ : ℝ} (hqual : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ F) ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real
      (allValue (C.successBits r m y) true ∩ F) ≤ (q : ℝ)^Box.successCard m r*γ/τ := by
  have hdis : Disjoint (G.outsideBits m C) (C.successBits r m y ∪ C.bits m) :=
    Finset.disjoint_union_right.mpr ⟨(G.successBits_disjoint_outside m C r hw hy).symm,
      G.outsideBits_disjoint_inside m C⟩
  have hdet : ProductCylinder.DeterminedBy (F := Prop) (C.successBits r m y ∪ C.bits m)
      (fun ω => ω ∈ allValue (C.successBits r m y) true ∩ F) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,
      allValue_determined _ _ ω ω' (fun e he => h e (Finset.mem_union_left _ he)),
      hF ω ω' (fun e he => h e (Finset.mem_union_right _ he))]
  rw [fixed_determined_probability p _ _ hdis ξ _ hdet]
  exact bad_success_mass m p q C r hw hy hp F hF hqual

end LatticeGraph
end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
theorem finite_measureReal_mono_ae {A B : Set Ω} (h : A ≤ᵐ[μ] B) :
    μ.real A ≤ μ.real B :=
  ENNReal.toReal_le_toReal (_root_.MeasureTheory.measure_ne_top μ A) (_root_.MeasureTheory.measure_ne_top μ B) |>.mpr (_root_.MeasureTheory.measure_mono_ae h)
end MeasureTheory

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem entrant_exterior {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : C.Exterior y :=
  (Finset.mem_filter.mp hy).2.choose_spec.1

theorem entrant_node {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : y ∈ G.vertices := (Finset.mem_filter.mp hy).1

/-- Actual separated seed trials under an arbitrary fixed outside pattern. -/
theorem fixed_large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex) (ξ : m.Config)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ)
    (hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real
      {ω | ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let pf := fixedParameter p (G.outsideBits m C) ξ
  let μ := ProductCylinder.law pf
  let c := (q : ℝ)^Box.successCard m r
  obtain ⟨t,ht,hcard,hsep⟩ := Box.separated_subset (G.entrants m C ξ o) r K hlarge
  let v (y : t) := G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y.1
  let F (y : t) := {ω | conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω ≤ 1-τ}
  let A (y : t) := allValue (C.successBits r m y.1) true
  let B (y : t) := A y ∩ F y
  have hy (y : t) : C.Exterior y.1 := G.entrant_exterior m (ht y.2)
  have hF (y : t) : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F y) := by
    intro ω ω' h
    simp only [F,Set.mem_ofPred_eq,conditionalProbability_determined p (C.bits m) _ ω ω' h]
  have hfresh (y : t) : ∀ e ∈ C.successBits r m y.1, pf e = q := by
    intro e he
    change fixedParameter p (G.outsideBits m C) ξ e = q
    rw [fixedParameter,ite_eq_right (Finset.disjoint_left.mp (G.successBits_disjoint_outside m C r hw (hy y)) he)]
    exact hp e (C.successBits_contained r m hw (hy y) he)
  have hmass (y : t) : μ.real (A y) = c := by
    rw [allValue_probability_constant pf _ q (hfresh y)]
    simp only [bitProbability,ite_true,C.successBits_card r m hw (hy y)]
    rfl
  have hpair (y z : t) (hyz : y ≠ z) : μ.real (A y ∩ A z) ≤ c*c := by
    have hd := C.successBits_disjoint r m hw (hy y) (hy z)
      (hsep y y.2 z z.2 (fun h => hyz (Subtype.ext h)))
    have hind := indepSet_determined pf _ _ hd (A y) (A z)
      (allValue_determined _ _) (allValue_determined _ _)
    have hh : μ.real (A y ∩ A z) = μ.real (A y)*μ.real (A z) := by
      simp only [Measure.real_def,μ,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
    rw [hh,hmass y,hmass z]
  have hbad (y : t) : μ.real (B y) ≤ c*γ/τ :=
    G.fixed_bad_success_mass m p q C r hw (hy y) ξ hp (F y) (hF y) (hqual y (hy y))
  have hbound := TrialCounts.no_good_probability μ A B
    (fun _ => measurableSet_allValue _ _)
    (fun y => (measurableSet_allValue _ _).inter (measurableSet_conditional_test _ _ _ _))
    (c := c) (γ := γ) (τ := τ)
    (by rw [Fintype.card_coe,hcard]; exact mul_pos (Nat.cast_pos.mpr hK) (pow_pos hq _))
    hτ hmass hpair hbad
  rw [Fintype.card_coe,hcard] at hbound
  apply (finite_measureReal_mono_ae (μ := μ) ?_).trans hbound
  filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
    (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
  intro hfail y hAy
  refine ⟨hAy,?_⟩
  by_contra hnot
  have hg : 1-τ < conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω :=
    lt_of_not_ge hnot
  have hyω : y.1 ∈ G.entrants m C ω o := hω.symm ▸ ht y.2
  let yn : G.Node := ⟨y.1,G.entrant_node m hyω⟩
  obtain ⟨u,hu,hconn⟩ := G.success_reaches_center m C r hw hC (y := yn) hyω hAy
  have huv : u = v y := Subtype.ext hu
  apply hfail
  refine ⟨u,?_,hconn⟩
  exact ⟨v y,congrArg Subtype.val huv.symm,hg⟩

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem measurableSet_large_entrants (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | L ≤ (G.entrants m C ω o).card} := by
  apply ProductCylinder.measurableSet_determined (G.outsideBits m C)
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,G.entrants_determined m C o ω ω' h]

/-- Integrating the exact separated-trial estimate, including histories with
fewer than L entries. -/
theorem large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real
      {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
        ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let E : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  have hm : MeasurableSet E := (G.measurableSet_large_entrants m C o _).inter
    (G.measurableSet_meets_goodRelays m p (C.bits m) o T τ).compl
  have hr := select_probability_le p (G.outsideBits m C) (fun _ => E) (fun _ => hm)
    (b := 4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ) ?_
  · exact hr
  · intro a
    let ξ := ProductCylinder.extend (G.outsideBits m C) a
    by_cases hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card
    · exact (measureReal_mono (fun _ h => h.2)).trans
        (G.fixed_large_entrants_failure m p q hq C r K hK hw hC o T ξ hp hτ hqual hlarge)
    · have he : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real E = 0 := by
        have hz : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)) E = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
            (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
          intro h
          exact hlarge (hω ▸ h.1)
        simp only [Measure.real_def,hz,ENNReal.toReal_zero]
      rw [he]
      positivity

end CriticalZ3.LatticeGraph

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem entryBit_internal_expand {C : Box} {y : Vertex} (hy : C.Exterior y) (m : Model) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand hy)
      (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
  · exact (mem_vertices _ _).mpr (C.contains_expand 1 (entry_spec hy).1)
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

/-- The shell + separated-seed + interior-quality extension, with all probability
terms explicit. The input seed events are the exact cube-restricted events. -/
theorem extension_bound (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ)) {p₀ : ℝ} (hqp : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1)
    (B : Box) (r K R : ℕ) (hK : 0 < K) (hrR : r < R)
    (hG : G.ContainsBox (B.expand R)) (o : G.Node) (T : Set Vertex)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ e ∈ (B.expand R).bits m, p e = q)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hreach : ∀ c, (B.expand R).Contains c → ∃ ℓ : ℕ,
      r ≤ ℓ ∧ G.ContainsBox (Box.cube c ℓ) ∧
      1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c r ℓ T)) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ≤
      1/((1-p₀)^(K*(8*r+5)^3)*(R-r : ℕ)) +
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ+τ := by
  have hsub (j : ℕ) (hj : j < R) : ∀ x, ((B.expand j).expand 1).Contains x →
      (B.expand R).Contains x := by
    intro x hx
    rw [Box.expand_expand] at hx
    exact B.expand_mono (by omega) hx
  obtain ⟨j,hj,hlayer⟩ := G.exists_shell m p B o q hqp hp₀ (K*(8*r+5)^3) r R hrR ho (by
    intro j hj y hy
    exact hp _ (Box.bits_mono m (hsub j (Finset.mem_Ico.mp hj).2) (Box.entryBit_internal_expand hy m)))
  let C := B.expand j
  have hjR : j < R := (Finset.mem_Ico.mp hj).2
  have hw : ∀ i, C.lower i+r ≤ C.upper i-r := B.expanded_seed_width (Finset.mem_Ico.mp hj).1
  have hC : G.ContainsBox (C.expand 1) := hG.mono G (hsub j hjR)
  have hpC : ∀ e ∈ (C.expand 1).bits m, p e = q := fun e he =>
    hp e (Box.bits_mono m (hsub j hjR) he)
  have hqual (y : Vertex) (_hy : C.Exterior y) : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ := by
    let c := C.relayCenter r y
    have hc : C.Contains c := C.seedBox_contained r hw y _ (Box.center_mem_cube _ _)
    obtain ⟨ℓ,hrℓ,hcube,hprob⟩ := hreach c (B.expand_mono hjR.le hc)
    have hmass : (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true) =
        (q : ℝ)^Box.seedCard m r := by
      rw [allValue_probability_constant p _ q (by
        intro e he
        exact hpC e (Box.bits_mono m (fun x hx => C.contains_expand 1
          (C.seedBox_contained r hw y x hx)) he))]
      simp only [bitProbability,ite_true,Box.seedBox,Box.cube_bits_card,Box.seedCard]
    have hh := G.seed_conditional_quality m p C T hrℓ (C.seedBox_contained r hw y)
      hcube (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) rfl hτ hprob
    change (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ _) ≤
      (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true)*γ/τ at hh
    rwa [hmass] at hh
  have hlarge := G.large_entrants_failure m p q hq C r K hK hw hC o T hpC hγ hτ hqual
  have hrelay := G.random_relay_failure m p (C.bits m) o T hτ.le
  let E₁ : Set m.Config := {ω | G.Meets m ω o {x | B.Contains x} ∧
    (G.entrants m C ω o).card < K*(8*r+5)^3}
  let E₂ : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  let E₃ : Set m.Config := {ω | G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω) ∧
    ¬G.Meets m ω o T}
  have hcontain : {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    intro ω hω
    by_cases hn : (G.entrants m C ω o).card < K*(8*r+5)^3
    · exact Or.inl (Or.inl ⟨hω.1,hn⟩)
    · by_cases hg : G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)
      · exact Or.inr ⟨hg,hω.2⟩
      · exact Or.inl (Or.inr ⟨le_of_not_gt hn,hg⟩)
  have hh := (measureReal_mono (μ := ProductCylinder.law p) hcontain).trans
    ((measureReal_union_le (E₁ ∪ E₂) E₃).trans
      (add_le_add (measureReal_union_le E₁ E₂) le_rfl))
  have := hh.trans (add_le_add (add_le_add hlayer hlarge) hrelay)
  simpa only [add_assoc] using this

end LatticeGraph
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

noncomputable def contourError : ℝ := (1/100 : ℝ)^7/2

theorem contourError_pos : 0 < contourError := by norm_num [contourError]
theorem contourError_lt_half : contourError < 1/2 := by norm_num [contourError]

theorem contour_power (n : ℕ) :
    (2*contourError)^((n : ℝ)/7) = (1/100 : ℝ)^n := by
  have he : 2*contourError = (1/100 : ℝ)^7 := by unfold contourError; ring
  rw [he,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/100)]
  have hn : (7 : ℝ)*((n : ℝ)/7) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hn,Real.rpow_natCast]

theorem contour_budget :
    (∑' n : ℕ, 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7)) < 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(3/100 : ℝ)‖ < 1)).mul_left 2
  have he (n : ℕ) : 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7) =
      2*((n : ℝ)*(3/100 : ℝ)^n) := by
    rw [contour_power]
    have hb : (3/100 : ℝ)^n = 3^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hb]
    ring
  simp_rw [he]
  rw [h.tsum_eq]
  norm_num

theorem error_budgets {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    ∃ δ η τ γ : ℝ,
      δ ∈ Set.Ioo 0 1 ∧ η ∈ Set.Ioo 0 1 ∧ τ ∈ Set.Ioo 0 1 ∧ γ ∈ Set.Ioo 0 1 ∧
      δ+52*η/δ < f ∧ τ < η/4 ∧ γ < δ ∧ 2*γ/τ < η/4 := by
  let δ := f/2
  let η := δ*f/208
  let τ := η/8
  let γ := min (δ/2) (τ*η/16)
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have he0 : 0 < η := by dsimp [η]; positivity
  have he1 : η < 1 := by dsimp [η]; nlinarith
  have ht0 : 0 < τ := by dsimp [τ]; positivity
  have ht1 : τ < 1 := by dsimp [τ]; linarith
  have hg0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hgd : γ ≤ δ/2 := min_le_left _ _
  have hge : γ ≤ τ*η/16 := min_le_right _ _
  refine ⟨δ,η,τ,γ,⟨hd0,hd1⟩,⟨he0,he1⟩,⟨ht0,ht1⟩,⟨hg0,by linarith⟩,?_,?_,?_,?_⟩
  · have heq : 52*η/δ = f/4 := by dsimp [η]; field_simp; ring
    rw [heq]
    dsimp [δ]
    linarith
  · dsimp [τ]; linarith
  · linarith
  · apply (div_lt_iff₀ ht0).mpr
    nlinarith

end CriticalScales

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model
noncomputable def law : (m : Model) → ℝ → Measure m.Config
  | .bond,p => bondLaw p
  | .site,p => siteLaw p

def InfiniteAt : (m : Model) → Vertex → Set m.Config
  | .bond,x => bondInfiniteAt x
  | .site,x => siteInfiniteAt x

def SeedInfinite : (m : Model) → Vertex → ℕ → Set m.Config
  | .bond,c,r => bondSeedInfinite c r
  | .site,c,r => siteSeedInfinite c r

instance law_probability (m : Model) (p : ℝ) : IsProbabilityMeasure (m.law p) := by
  cases m <;> dsimp [law] <;> infer_instance

theorem law_eq_product (m : Model) (p : ℝ) :
    m.law p = ProductCylinder.law (fun _ => parameter p) := by cases m <;> rfl

theorem law_coe_eq_product (m : Model) (q : Set.Icc (0 : ℝ) 1) :
    m.law q = ProductCylinder.law (fun _ => q) := by
  rw [law_eq_product]
  have h : parameter (q : ℝ) = q := Subtype.ext (parameter_coe q.property)
  rw [h]

theorem exists_seed (m : Model) {p ε : ℝ} (hp : 0 < m.law p (m.InfiniteAt 0)) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ (m.law p).real (m.SeedInfinite 0 r)ᶜ < ε^24 := by
  cases m
  · exact exists_bondSeed hp hε
  · exact exists_siteSeed hp hε

theorem lower_quarterFaces (m : Model) {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {r : ℕ} (hseed : (m.law p).real (m.SeedInfinite 0 r)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, r ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (m.law q).real (m.SeedReaches c r n (QuarterFace c n f)) := by
  cases m
  · simpa only [law,seedReaches_bond] using bond_lower_quarterFaces hp hγ hseed s hs
  · exact site_lower_quarterFaces hp hγ hseed s hs
end Model

structure ScaleData (model : Model) where
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  q : Set.Icc (0 : ℝ) 1
  q_half : p/2 < (q : ℝ)
  q_lt : (q : ℝ) < p
  δ : ℝ
  η : ℝ
  τ : ℝ
  γ : ℝ
  δ_range : δ ∈ Set.Ioo 0 1
  η_range : η ∈ Set.Ioo 0 1
  τ_range : τ ∈ Set.Ioo 0 1
  γ_range : γ ∈ Set.Ioo 0 1
  failure_budget : δ+52*η/δ < CriticalScales.contourError
  relay_budget : τ < η/4
  γδ : γ < δ
  trial_budget : 2*γ/τ < η/4
  seed : ℕ
  K : ℕ
  R : ℕ
  r : ℕ
  seed_pos : 0 < seed
  K_pos : 0 < K
  seed_R : seed < R
  large_r : 100*(R+1) < r
  K_budget : 4/((K:ℝ)*(p/2)^(Box.seedCard model seed+1)) < η/4
  R_budget : 1/((1-p)^(K*(8*seed+5)^3)*(R-seed:ℕ)) < η/4
  faces : ∀ n ∈ ({2*r,2*r+1,10*r} : Finset ℕ), ∀ c f,
    1-γ < (ProductCylinder.law (fun _ : model.Bit => q)).real
      (model.SeedReaches c seed n (QuarterFace c n f))

theorem exists_scales (model : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < model.law p (model.InfiniteAt 0)) : ∃ s : ScaleData model, s.p = p := by
  obtain ⟨δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb⟩ := CriticalScales.error_budgets
    CriticalScales.contourError_pos (CriticalScales.contourError_lt_half.trans (by norm_num))
  obtain ⟨a,ha,hseed⟩ := model.exists_seed hInf (show 0 < γ/2 by linarith [hγ.1])
  let ρ : ℝ := (p/2)^(Box.seedCard model a+1)
  have hρ : 0 < ρ := pow_pos (by linarith) _
  obtain ⟨K,hK⟩ := exists_nat_gt (16/(ρ*η))
  have hK0 : 0 < K := by
    have : 0 < (K:ℝ) := (div_pos (by norm_num) (mul_pos hρ hη.1)).trans hK
    exact_mod_cast this
  have hKb : 4/((K:ℝ)*ρ) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hρ hη.1)).mp hK
    apply (div_lt_iff₀ (mul_pos (by exact_mod_cast hK0) hρ)).mpr
    nlinarith
  let α : ℝ := (1-p)^(K*(8*a+5)^3)
  have hα : 0 < α := pow_pos (by linarith) _
  obtain ⟨d,hd⟩ := exists_nat_gt (4/(α*η))
  have hd0 : 0 < d := by
    have : 0 < (d:ℝ) := (div_pos (by norm_num) (mul_pos hα hη.1)).trans hd
    exact_mod_cast this
  let R := a+d
  have haR : a < R := by dsimp [R]; omega
  have hRb : 1/(α*(R-a:ℕ)) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hα hη.1)).mp hd
    have he : R-a = d := by dsimp [R]; omega
    rw [he]
    apply (div_lt_iff₀ (mul_pos hα (by exact_mod_cast hd0))).mpr
    nlinarith
  let r := 100*(R+1)+1
  have hlr : 100*(R+1) < r := by dsimp [r]; omega
  have har : a ≤ r := by omega
  obtain ⟨q,hq,hfaces⟩ := model.lower_quarterFaces hp hγ.1 hseed
    {2*r,2*r+1,10*r} (by intro n hn; simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega)
  let q' : Set.Icc (0:ℝ) 1 := ⟨q,⟨by linarith [hq.1],le_of_lt (hq.2.trans hp1)⟩⟩
  refine ⟨⟨p,hp,hp1,q',hq.1,hq.2,δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb,
    a,K,R,r,ha,hK0,haR,hlr,hKb,hRb,?_⟩,rfl⟩
  intro n hn c f
  have hh := hfaces n hn c f
  rw [show q = (q':ℝ) from rfl,model.law_coe_eq_product q'] at hh
  exact hh

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem q_pos : 0 < (s.q:ℝ) := (half_pos s.p_pos).trans s.q_half

theorem successCard_le : Box.successCard model s.seed ≤ Box.seedCard model s.seed+1 := by
  cases model <;> simp [Box.successCard]

theorem success_bound : (s.p/2)^(Box.seedCard model s.seed+1) ≤
    (s.q:ℝ)^Box.successCard model s.seed := by
  exact (pow_le_pow_left₀ (by linarith [s.p_pos]) s.q_half.le _).trans
    (pow_le_pow_of_le_one s.q.property.1 s.q.property.2 s.successCard_le)

theorem extension_budget :
    1/((1-s.p)^(s.K*(8*s.seed+5)^3)*(s.R-s.seed:ℕ)) +
      4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed)+2*s.γ/s.τ+s.τ < s.η := by
  have hh : 4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed) ≤
      4/((s.K:ℝ)*(s.p/2)^(Box.seedCard model s.seed+1)) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by exact_mod_cast s.K_pos) (pow_pos (half_pos s.p_pos) _))
    exact mul_le_mul_of_nonneg_left s.success_bound (Nat.cast_nonneg _)
  linarith [s.R_budget,s.K_budget,s.trial_budget,s.relay_budget]
end ScaleData
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace LatticeRelay
open Set
abbrev Vertex := Fin 3 → ℤ

def Rect (c w : Vertex) : Set Vertex := {x | ∀ i, |x i - c i| ≤ w i}
def Cube (c : Vertex) (s : ℤ) : Set Vertex := Rect c (fun _ => s)
def Expand (c w : Vertex) (R : ℤ) : Set Vertex := Rect c (fun i => w i + R)
def DirectedInterval (a s : ℤ) (positive : Bool) (b : ℤ) : Prop :=
  if positive then a ≤ b ∧ b ≤ a+s else a-s ≤ b ∧ b ≤ a

def QuarterFace (u : Vertex) (s : ℤ) (normal : Fin 3) (signs : Fin 3 → Bool) : Set Vertex :=
  {x | x normal = u normal + (if signs normal then s else -s) ∧
    ∀ i, i ≠ normal → DirectedInterval (u i) s (signs i) (x i)}

def inward (u : Vertex) : Fin 3 → Bool := fun i => decide (u i < 0)

def Prism (r : ℤ) : Set Vertex :=
  {x | -10*r ≤ x 0 ∧ x 0 ≤ 30*r+1 ∧
    ∀ i : Fin 3, i ≠ 0 → |x i| ≤ 10*r}

theorem inward_endpoint_bound {a s W : ℤ} (_hs : 0 ≤ s) (hW : s ≤ W)
    (ha : |a| ≤ W+s) : |a + (if decide (a < 0) then s else -s)| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [h] <;> omega

theorem inward_interval_bound {a b s W : ℤ} (hW : s ≤ W) (ha : |a| ≤ W)
    (hb : DirectedInterval a s (decide (a < 0)) b) : |b| ≤ W := by
  rw [abs_le] at ha ⊢
  by_cases h : a < 0 <;> simp [DirectedInterval,h] at hb <;> omega

theorem quarterFace_subset_cube {u : Vertex} {s : ℤ} (hs : 0 ≤ s)
    (h : Fin 3) (signs : Fin 3 → Bool) : QuarterFace u s h signs ⊆ Cube u s := by
  intro x hx i
  by_cases hi : i = h
  · subst i
    rw [hx.1]
    dsimp
    cases signs h <;> simp [abs_of_nonneg hs]
  · have hh := hx.2 i hi
    change |x i - u i| ≤ s
    rw [abs_le]
    unfold DirectedInterval at hh
    cases hsi : signs i <;> simp [hsi] at hh <;> omega

theorem quarterFace_nonempty {u : Vertex} {s : ℤ} (hs : 0 ≤ s)
    (h : Fin 3) (signs : Fin 3 → Bool) : (QuarterFace u s h signs).Nonempty := by
  let x : Vertex := fun i => if i = h then u i + (if signs h then s else -s) else u i
  refine ⟨x,by simp [x],?_⟩
  intro i hi
  dsimp [x]
  rw [ite_eq_right hi]
  cases signs i <;> simp [DirectedInterval] <;> omega

/-- Generic form of one of the three contraction steps. -/
theorem contraction_face {r a : ℤ} (hr : 0 ≤ r) (ha : 0 ≤ a) (h : Fin 3)
    {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    QuarterFace u (2*r) h (inward u) ⊆
      Rect 0 (fun i => if i ≤ h then 2*r+a else 4*r+a) := by
  intro x hx i
  change |x i - 0| ≤ _
  rw [sub_zero]
  by_cases hi : i = h
  · subst i
    rw [hx.1]
    simp only [le_refl,ite_true,inward]
    apply inward_endpoint_bound (by omega) (by omega)
    have huu := hu h
    simp only [lt_self_iff_false,ite_false] at huu
    omega
  · have hh := hx.2 i hi
    dsimp [inward] at hh
    apply inward_interval_bound (by dsimp; split_ifs <;> omega) _ hh
    have hhi : (i < h) ↔ (i ≤ h) := by omega
    simpa only [hhi] using hu i

theorem contraction_cube {r a : ℤ} (_hr : 0 ≤ r) (ha : 0 ≤ a)
    (ha' : 6*r+a < 10*r) (h : Fin 3) {u : Vertex}
    (hu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a) :
    Cube u (2*r) ⊆ Prism r := by
  intro x hx
  have hu' (i : Fin 3) : |u i| ≤ 4*r+a := by
    have hu' := hu i
    split_ifs at hu' <;> omega
  have hxi (i : Fin 3) : |x i| < 10*r := by
    have hxu := hx i
    change |x i-u i| ≤ 2*r at hxu
    have huu := hu' i
    rw [abs_le] at hxu huu
    rw [abs_lt]
    omega
  have h0 := (abs_lt.mp (hxi 0))
  refine ⟨by omega,by omega,?_⟩
  intro i _
  exact (hxi i).le

def axisCenter (a : ℤ) : Vertex := fun i => if i = 0 then a else 0

def forwardInward (u : Vertex) : Fin 3 → Bool :=
  fun i => if i = 0 then true else decide (u i < 0)

/-- Generic form of each of the ten translation steps, including the final
length 2r+1 step. -/
theorem translation_face {a s w : ℤ} (hs : s ≤ w) {u : Vertex}
    (hu : u ∈ Cube (axisCenter a) w) :
    QuarterFace u s 0 (forwardInward u) ⊆ Cube (axisCenter (a+s)) w := by
  intro x hx i
  by_cases hi : i = 0
  · subst i
    have huu := hu 0
    rw [hx.1]
    simpa [forwardInward,axisCenter] using huu
  · have huu := hu i
    have hxx := hx.2 i hi
    simp only [forwardInward,hi,ite_false] at hxx
    simp only [axisCenter,hi,ite_false,sub_zero] at huu ⊢
    exact inward_interval_bound hs huu hxx

theorem translation_cube {r R a s w : ℤ}
    (_hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R) (hs : s ≤ 2*r+1)
    {u : Vertex} (hu : u ∈ Cube (axisCenter a) w) :
    Cube u s ⊆ Prism r := by
  intro x hx
  have bounds (i : Fin 3) : -(w+s) ≤ x i-axisCenter a i ∧
      x i-axisCenter a i ≤ w+s := by
    have hu' := (abs_le.mp (hu i))
    have hx' := (abs_le.mp (hx i))
    dsimp at hu' hx'
    omega
  have h0 := bounds 0
  simp only [axisCenter,ite_true] at h0
  refine ⟨by omega,by omega,?_⟩
  intro i hi
  have h := bounds i
  simp only [axisCenter,hi,ite_false,sub_zero] at h
  rw [abs_le]
  constructor <;> omega

def contractionWidths (r R : ℤ) (t : ℕ) : Vertex :=
  fun h => if h.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R

def HasInterface (r R : ℤ) (c w : Vertex) (T : Set Vertex) : Prop :=
  ∀ u ∈ Expand c w R, ∃ s : ℤ, s ∈ ({2*r,2*r+1,10*r} : Set ℤ) ∧
    Cube u s ⊆ Prism r ∧ ∃ h signs, QuarterFace u s h signs ⊆ T

theorem contraction_interface {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {t : ℕ} (ht : t < 3) :
    HasInterface r R 0 (contractionWidths r R t)
      (Rect 0 (contractionWidths r R (t+1))) := by
  intro u hu
  let h : Fin 3 := ⟨t,ht⟩
  let a : ℤ := (t+1)*R
  have ht' : (t : ℤ) < 3 := by exact_mod_cast ht
  have ht0 : (0 : ℤ) ≤ t := by positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha3 : a ≤ 3*R := by dsimp [a]; nlinarith
  have huu : ∀ i, |u i| ≤ if i < h then 2*r+a else 4*r+a := by
    intro i
    have hh := hu i
    change |u i-0| ≤ (if i.val < t then 2*r+(t : ℤ)*R else 4*r+(t : ℤ)*R)+R at hh
    change |u i| ≤ if i.val < t then 2*r+a else 4*r+a
    dsimp [a]
    rw [add_mul]
    by_cases hi : i.val < t <;> simp only [hi,ite_true,ite_false,sub_zero,one_mul] at * <;> omega
  refine ⟨2*r,by simp,contraction_cube (by omega) ha0 (by omega) h huu,h,inward u,?_⟩
  intro x hx i
  have hb := contraction_face (by omega) ha0 h huu hx i
  change |x i-0| ≤ if i.val < t+1 then 2*r+(↑(t+1) : ℤ)*R else 4*r+(↑(t+1) : ℤ)*R
  have hi : (i ≤ h) ↔ i.val < t+1 := by change (i.val ≤ t) ↔ _; omega
  simpa only [hi,a,Nat.cast_add,Nat.cast_one,Pi.zero_apply] using hb

theorem translation_interface {r R a s w : ℤ}
    (hR : 0 < R) (hr : 100*(R+1) < r)
    (ha0 : 0 ≤ a) (ha : a ≤ 18*r) (hw : w ≤ 2*r+13*R)
    (hs : s = 2*r ∨ s = 2*r+1) (hsw : s ≤ w) :
    HasInterface r R (axisCenter a) (fun _ => w-R) (Cube (axisCenter (a+s)) w) := by
  intro u hu
  have huu : u ∈ Cube (axisCenter a) w := by
    intro i
    simpa only [Expand,Rect,sub_add_cancel] using hu i
  refine ⟨s,?_,translation_cube hR hr ha0 ha hw (by rcases hs with rfl|rfl <;> omega) huu,
    0,forwardInward u,translation_face hsw huu⟩
  rcases hs with rfl|rfl <;> simp

def routeCenter (r : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then 0 else axisCenter (if i ≤ 12 then 2*r*(i-3 : ℕ) else 20*r+1)
def routeWidths (r R : ℤ) (i : ℕ) : Vertex :=
  if i ≤ 3 then contractionWidths r R i else fun _ => 2*r+(i : ℤ)*R

def P (r R : ℤ) (i : ℕ) : Set Vertex := Rect (routeCenter r i) (routeWidths r R i)

@[simp] theorem axisCenter_zero : axisCenter 0 = 0 := by ext i; simp [axisCenter]

theorem routeCenter_translation {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r i = axisCenter (2*r*(i-3 : ℕ)) := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    simp [routeCenter]
  · simp [routeCenter,h,hi']

theorem routeWidths_translation {r R : ℤ} {i : ℕ} (hi : 3 ≤ i) :
    routeWidths r R i = fun _ => 2*r+(i : ℤ)*R := by
  by_cases h : i ≤ 3
  · have : i = 3 := by omega
    subst i
    funext j
    simp [routeWidths,contractionWidths,j.isLt]
  · simp [routeWidths,h]

def stepSize (r : ℤ) (i : ℕ) : ℤ := if i < 12 then 2*r else 2*r+1

theorem routeCenter_next {r : ℤ} {i : ℕ} (hi : 3 ≤ i) (hi' : i ≤ 12) :
    routeCenter r (i+1) = axisCenter (2*r*(i-3 : ℕ)+stepSize r i) := by
  by_cases h : i < 12
  · rw [routeCenter_translation (by omega) (by omega)]
    congr 1
    simp only [stepSize,h,ite_true,Nat.cast_sub (by omega : 3 ≤ i),
      Nat.cast_sub (by omega : 3 ≤ i+1),Nat.cast_add,Nat.cast_one]
    ring
  · have : i = 12 := by omega
    subst i
    simp only [routeCenter,show ¬13 ≤ 3 by omega,ite_false,show ¬13 ≤ 12 by omega,
      stepSize,lt_self_iff_false]
    congr 1
    norm_num
    ring

theorem thirteen_interfaces {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    HasInterface r R (routeCenter r i) (routeWidths r R i) (P r R (i+1)) := by
  by_cases hi3 : i < 3
  · simpa only [P,routeCenter,routeWidths,show i ≤ 3 by omega,show i+1 ≤ 3 by omega,
      ite_true] using contraction_interface hR hr hi3
  · have hil : 3 ≤ i := by omega
    have hii : i ≤ 12 := by omega
    rw [routeCenter_translation hil hii,routeWidths_translation hil]
    unfold P
    rw [routeCenter_next hil hii,routeWidths_translation (by omega)]
    let a : ℤ := 2*r*(i-3 : ℕ)
    let w : ℤ := 2*r+(↑(i+1) : ℤ)*R
    have hir : (i : ℤ) ≤ 12 := by exact_mod_cast hii
    have hilr : (3 : ℤ) ≤ i := by exact_mod_cast hil
    have hr0 : 0 ≤ r := by omega
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have ha : a ≤ 18*r := by
      dsimp [a]
      rw [Nat.cast_sub hil]
      norm_num
      nlinarith
    have hw : w ≤ 2*r+13*R := by dsimp [w]; nlinarith
    have hs : stepSize r i = 2*r ∨ stepSize r i = 2*r+1 := by
      unfold stepSize; split_ifs <;> simp
    have hsw : stepSize r i ≤ w := by
      dsimp [w]
      rcases hs with h|h <;> rw [h] <;> nlinarith
    have he : (fun _ : Fin 3 => 2*r+(i : ℤ)*R) = fun _ => w-R := by
      funext j
      dsimp [w]
      ring
    rw [he]
    exact translation_interface hR hr ha0 ha hw hs hsw

@[simp] theorem P_zero (r R : ℤ) : P r R 0 = Cube 0 (4*r) := by
  simp only [P,routeCenter,routeWidths,Nat.zero_le,show 0 ≤ 3 by omega,ite_true,Cube]
  congr 1
  funext i
  simp [contractionWidths]

theorem P_thirteen_subset {r R : ℤ} (_hR : 0 < R) (hr : 100*(R+1) < r) :
    P r R 13 ⊆ Cube (axisCenter (20*r+1)) (4*r) := by
  intro x hx i
  have h := hx i
  simp only [routeCenter,routeWidths,show ¬13 ≤ 3 by omega,ite_false,
    show ¬13 ≤ 12 by omega] at h
  change |x i-axisCenter (20*r+1) i| ≤ 4*r
  dsimp at h
  omega

theorem expanded_route_subset_prism {r R : ℤ} (hR : 0 < R) (hr : 100*(R+1) < r)
    {i : ℕ} (hi : i < 13) :
    Expand (routeCenter r i) (routeWidths r R i) R ⊆ Prism r := by
  intro u hu
  obtain ⟨s,hs,hsub,_⟩ := thirteen_interfaces hR hr hi u hu
  apply hsub
  intro j
  change |u j-u j| ≤ s
  simp only [sub_self,abs_zero]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hs
  rcases hs with rfl|rfl|rfl <;> omega

end LatticeRelay

end OAI
end
end

section
section
namespace OAI


open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model

def Internal : (m : Model) → Set Vertex → m.Bit → Prop
  | .bond,D,e => e.1 ∈ D ∧ step e.1 e.2 ∈ D
  | .site,D,x => x ∈ D

def UniformOn (m : Model) (p : m.Bit → Set.Icc (0:ℝ) 1)
    (q : Set.Icc (0:ℝ) 1) (D : Set Vertex) : Prop := ∀ e, m.Internal D e → p e = q

theorem box_internal (m : Model) (B : Box) (e : m.Bit) :
    e ∈ B.bits m ↔ m.Internal {x | B.Contains x} e := by
  cases m <;> simp [Box.bits,Internal]

theorem internal_mono (m : Model) {D T : Set Vertex} (h : D ⊆ T) {e : m.Bit}
    (he : m.Internal D e) : m.Internal T e := by
  cases m
  · exact ⟨h he.1,h he.2⟩
  · exact h he

theorem UniformOn.box (m : Model) {p : m.Bit → Set.Icc (0:ℝ) 1} {q : Set.Icc (0:ℝ) 1}
    {D : Set Vertex} (h : m.UniformOn p q D) (B : Box) (hB : ∀ x, B.Contains x → x ∈ D) :
    ∀ e ∈ B.bits m, p e = q := fun e he => h e (m.internal_mono hB ((m.box_internal B e).mp he))

theorem seedReaches_target_mono (m : Model) (c : Vertex) (a b : ℕ) {T U : Set Vertex} (h : T ⊆ U) :
    m.SeedReaches c a b T ⊆ m.SeedReaches c a b U := by
  rintro ω ⟨x,hx,ho,y,hy,hp⟩
  exact ⟨x,hx,ho,y,h hy,hp⟩

theorem seedReaches_image_probability (m : Model) (S : SignedSymmetry) (q : Set.Icc (0:ℝ) 1)
    (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    (ProductCylinder.law (fun _ : m.Bit => q)).real
      (m.SeedReaches (S.vertex c) a b (S.vertex '' T)) =
    (ProductCylinder.law (fun _ : m.Bit => q)).real (m.SeedReaches c a b T) := by
  have he : S.vertex ⁻¹' (S.vertex '' T) = T := Set.preimage_image_eq T S.vertex.injective
  cases m
  · simp only [seedReaches_bond,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.bond q (bondSeedReaches c a b T)
      (measurableSet_bondSeedReaches _ _ _ _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.bondSeedReaches_map ω c a b (S.vertex '' T)).symm
  · simp only [seedReaches_site,Measure.real_def]
    have hh := ProductCylinder.reindex_probability S.vertex q (siteSeedReaches c a b T)
      (measurableSet_siteSeedReaches _ _ _ hab _)
    rw [←hh]
    congr 2
    ext ω
    simpa only [Set.mem_preimage,he] using (S.siteSeedReaches_map ω c a b (S.vertex '' T)).symm
end Model

namespace LatticeGraph
variable (G : LatticeGraph)
def ContainsSet (D : Set Vertex) : Prop :=
  (∀ x ∈ D, x ∈ G.vertices) ∧ ∀ e : Bond, e.1 ∈ D → step e.1 e.2 ∈ D → e ∈ G.edges

theorem ContainsSet.box {D : Set Vertex} (h : G.ContainsSet D) (B : Box)
    (hB : ∀ x, B.Contains x → x ∈ D) : G.ContainsBox B := by
  constructor
  · intro x hx; exact h.1 x (hB x (Box.mem_vertices B x |>.mp hx))
  · intro e he
    have hh := (Box.mem_bonds B e).mp he
    exact h.2 e (hB _ hh.1) (hB _ hh.2)
end LatticeGraph

namespace Box

def rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  ⟨fun i => c i-w i,fun i => c i+w i,fun i => by linarith [hw i]⟩

theorem contains_rect (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (rect c w hw).Contains x ↔ x ∈ LatticeRelay.Rect c w := by
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ w i
    rw [abs_le]
    dsimp [rect] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ w i at hh
    rw [abs_le] at hh
    change c i-w i ≤ x i ∧ x i ≤ c i+w i
    omega

def framedRect (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) : Box :=
  rect (S.vertex c) (fun i => w (S.perm i)) (fun i => hw (S.perm i))

theorem abs_vertex_sub (S : SignedSymmetry) (x c : Vertex) (i : Fin 3) :
    |S.vertex x i-S.vertex c i| = |x (S.perm i)-c (S.perm i)| := by
  dsimp [SignedSymmetry.vertex]
  cases S.signs i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · have he : S.shift i+-x (S.perm i)-(S.shift i+-c (S.perm i)) =
        -(x (S.perm i)-c (S.perm i)) := by ring
    rw [he,abs_neg]
  · congr 1; ring

theorem framedRect_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i) (x : Vertex) :
    (framedRect S c w hw).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Rect c w := by
  rw [framedRect,contains_rect]
  change (∀ i, |S.vertex x i-S.vertex c i| ≤ w (S.perm i)) ↔ _
  simp_rw [abs_vertex_sub]
  constructor
  · intro h i; simpa only [Equiv.apply_symm_apply] using h (S.perm.symm i)
  · intro h i; exact h _

theorem framedRect_expand_map (S : SignedSymmetry) (c w : Vertex) (hw : ∀ i, 0 ≤ w i)
    (R : ℕ) (x : Vertex) :
    ((framedRect S c w hw).expand R).Contains (S.vertex x) ↔ x ∈ LatticeRelay.Expand c w R := by
  have he : (framedRect S c w hw).expand R =
      framedRect S c (fun i => w i+R) (fun i => by have := hw i; positivity) := by
    apply Box.ext <;> funext i <;> dsimp [expand,framedRect,rect] <;> ring
  rw [he,framedRect_map]
  rfl
end Box

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem radius_seed {n : ℕ} (hn : n ∈ ({2*s.r,2*s.r+1,10*s.r} : Finset ℕ)) : s.seed ≤ n := by
  have := s.seed_R
  have := s.large_r
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

theorem extension_interface (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (D : Set Vertex) (hG : G.ContainsSet D) (hp : model.UniformOn p s.q D)
    (o : G.Node) (ho : o.1 ∉ D) (B : Box) (T : Set Vertex)
    (hB : ∀ x, (B.expand s.R).Contains x → x ∈ D)
    (hI : ∀ u, (B.expand s.R).Contains u → ∃ n ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ),
      ∃ S : SignedSymmetry, ∃ c : Vertex, ∃ f : FaceIndex, S.vertex c = u ∧
      (∀ x ∈ cube u n, x ∈ D) ∧ S.vertex '' QuarterFace c n f ⊆ T) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | B.Contains x} ∧
      ¬G.Meets model ω o T} < s.η := by
  refine (G.extension_bound model p s.q s.q_pos s.q_lt.le s.p_lt_one B s.seed s.K s.R
    s.K_pos s.seed_R (hG.box G _ hB) o T (fun h => ho (hB _ h))
    (hp.box model _ hB) s.γ_range.1.le s.τ_range.1 ?_).trans_lt s.extension_budget
  intro u hu
  obtain ⟨n,hn,S,c,f,hc,hcube,hface⟩ := hI u hu
  have hr := s.radius_seed hn
  refine ⟨n,hr,hG.box G _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)),?_⟩
  have he := ProductCylinder.probability_congr_parameters ((Box.cube u n).bits model)
    p (fun _ => s.q) (hp.box model _ (fun x hx => hcube x (Box.contains_cube_iff.mp hx)))
    (model.SeedReaches u s.seed n T) (model.seedReaches_determined _ _ _ hr _)
  rw [he]
  have hh := s.faces n hn c f
  rw [←model.seedReaches_image_probability S s.q c s.seed n hr (QuarterFace c n f),hc] at hh
  exact hh.le.trans (measureReal_mono (model.seedReaches_target_mono _ _ _ hface))
end ScaleData
end CriticalZ3

namespace MeasureTheory
open scoped _root_.MeasureTheory
open Classical
variable {Ω : Type uOmega} [MeasurableSpace Ω]
theorem finite_relay_bound (μ : _root_.MeasureTheory.Measure Ω) [_root_.MeasureTheory.IsProbabilityMeasure μ] (A : ℕ → Set Ω)
    (η : ℝ) (n : ℕ) (h : ∀ i < n, μ.real (A i \ A (i+1)) ≤ η) :
    μ.real (A 0 \ A n) ≤ n*η := by
  induction n with
  | zero => simp only [Nat.cast_zero,zero_mul,Set.sdiff_self,_root_.MeasureTheory.measureReal_empty,le_refl]
  | succ n ih =>
    have hs : A 0 \ A (n+1) ⊆ (A 0 \ A n) ∪ (A n \ A (n+1)) := by
      intro ω hω
      by_cases hn : ω ∈ A n
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    have hh := (_root_.MeasureTheory.measureReal_mono (μ := μ) hs).trans (_root_.MeasureTheory.measureReal_union_le _ _)
    have hi := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    rw [Nat.cast_add,Nat.cast_one]
    nlinarith
end MeasureTheory

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem R_pos : 0 < s.R := s.seed_pos.trans s.seed_R

theorem route_width_nonneg (i : ℕ) (j : Fin 3) : 0 ≤ LatticeRelay.routeWidths s.r s.R i j := by
  unfold LatticeRelay.routeWidths
  split_ifs
  · dsimp [LatticeRelay.contractionWidths]
    split_ifs <;> positivity
  · positivity

def routeBox (S : SignedSymmetry) (i : ℕ) : Box :=
  Box.framedRect S (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i)
    (s.route_width_nonneg i)

theorem routeBox_contains (S : SignedSymmetry) (i : ℕ) (x : Vertex) :
    (s.routeBox S i).Contains x ↔ x ∈ S.vertex '' LatticeRelay.P s.r s.R i := by
  rw [←S.vertex.apply_symm_apply x,routeBox,Box.framedRect_map]
  simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
  rfl

theorem relay_in_frame (G : LatticeGraph) (p : model.Bit → Set.Icc (0:ℝ) 1)
    (S : SignedSymmetry) (hG : G.ContainsSet (S.vertex '' LatticeRelay.Prism s.r))
    (hp : model.UniformOn p s.q (S.vertex '' LatticeRelay.Prism s.r))
    (o : G.Node) (ho : o.1 ∉ S.vertex '' LatticeRelay.Prism s.r) :
    (ProductCylinder.law p).real
      {ω | G.Meets model ω o (cube (S.vertex 0) (4*s.r)) ∧
        ¬G.Meets model ω o (cube (S.vertex (LatticeRelay.axisCenter (20*s.r+1))) (4*s.r))}
      ≤ 13*s.η := by
  have hR : (0:ℤ) < s.R := by exact_mod_cast s.R_pos
  have hr : (100:ℤ)*(s.R+1) < s.r := by exact_mod_cast s.large_r
  have hcube (c : Vertex) (n : ℕ) : S.vertex '' LatticeRelay.Cube c n = cube (S.vertex c) n := by
    ext x
    rw [←S.vertex.apply_symm_apply x]
    simp only [Set.mem_image,Equiv.apply_eq_iff_eq,exists_eq_right]
    rw [←S.cube_map]
    rw [mem_cube]
    constructor <;> intro h i
    · have hh := h i
      change |S.vertex.symm x i-c i| ≤ (n:ℤ) at hh
      rw [abs_le] at hh
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n
      omega
    · have hh := h i
      change c i-n ≤ S.vertex.symm x i ∧ S.vertex.symm x i ≤ c i+n at hh
      change |S.vertex.symm x i-c i| ≤ (n:ℤ)
      rw [abs_le]
      omega
  let A (i : ℕ) : Set model.Config := {ω | G.Meets model ω o {x | (s.routeBox S i).Contains x}}
  have hi (i : ℕ) (hi : i < 13) : (ProductCylinder.law p).real (A i \ A (i+1)) ≤ s.η := by
    apply le_of_lt
    apply s.extension_interface G p (S.vertex '' LatticeRelay.Prism s.r) hG hp o ho
      (s.routeBox S i) {x | (s.routeBox S (i+1)).Contains x}
    · intro x hx
      refine ⟨S.vertex.symm x,?_,S.vertex.apply_symm_apply x⟩
      apply LatticeRelay.expanded_route_subset_prism hR hr hi
      apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm x)).mp
      simpa only [routeBox,Equiv.apply_symm_apply] using hx
    · intro u hu
      have huu : S.vertex.symm u ∈ LatticeRelay.Expand
          (LatticeRelay.routeCenter s.r i) (LatticeRelay.routeWidths s.r s.R i) s.R := by
        apply (Box.framedRect_expand_map S _ _ (s.route_width_nonneg i) s.R (S.vertex.symm u)).mp
        simpa only [routeBox,Equiv.apply_symm_apply] using hu
      obtain ⟨n,hn,hsub,j,signs,hface⟩ := LatticeRelay.thirteen_interfaces hR hr hi _ huu
      have hn' : ∃ l ∈ ({2*s.r,2*s.r+1,10*s.r}:Finset ℕ), (l:ℤ) = n := by
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hn
        rcases hn with rfl|rfl|rfl
        · exact ⟨2*s.r,by simp,by push_cast; rfl⟩
        · exact ⟨2*s.r+1,by simp,by push_cast; rfl⟩
        · exact ⟨10*s.r,by simp,by push_cast; rfl⟩
      obtain ⟨l,hl,rfl⟩ := hn'
      refine ⟨l,hl,S,S.vertex.symm u,(j,signs),S.vertex.apply_symm_apply u,?_,?_⟩
      · intro x hx
        have hx' : x ∈ S.vertex '' LatticeRelay.Cube (S.vertex.symm u) l := by
          rw [hcube,S.vertex.apply_symm_apply]
          exact hx
        obtain ⟨y,hy,rfl⟩ := hx'
        exact ⟨y,hsub hy,rfl⟩
      · rintro x ⟨y,hy,rfl⟩
        apply (s.routeBox_contains S (i+1) _).mpr
        exact ⟨y,hface hy,rfl⟩
  have h := finite_relay_bound (ProductCylinder.law p) A s.η 13 hi
  norm_num only [Nat.cast_ofNat] at h
  apply le_trans (measureReal_mono (μ := ProductCylinder.law p) ?_) h
  intro ω hω
  constructor
  · obtain ⟨y,hy,hconn⟩ := hω.1
    refine ⟨y,?_,hconn⟩
    apply (s.routeBox_contains S 0 _).mpr
    rw [LatticeRelay.P_zero,show (4:ℤ)*s.r = (4*s.r:ℕ) by push_cast; rfl,hcube]
    exact hy
  · intro hh
    apply hω.2
    obtain ⟨y,hy,hconn⟩ := hh
    refine ⟨y,?_,hconn⟩
    have hy' := (s.routeBox_contains S 13 _).mp hy
    obtain ⟨z,hz,hzy⟩ := hy'
    rw [←hzy]
    have hz' := LatticeRelay.P_thirteen_subset hR hr hz
    have hm : S.vertex z ∈ S.vertex '' LatticeRelay.Cube (LatticeRelay.axisCenter (20*s.r+1)) (4*s.r:ℕ) :=
      ⟨z,by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hz',rfl⟩
    rwa [hcube] at hm
end ScaleData
end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology

open scoped ENNReal BigOperators Matrix

/-! Finite balanced directed boundaries admit closed edge-simple trails.
This is used only for the planar contour dependency of the main proof. -/
open Classical Function
namespace FiniteTrails
variable {D : Type uD} {V : Type uV} [Fintype D]

noncomputable def successor (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v}) :
    Equiv.Perm D :=
  (Equiv.sigmaFiberEquiv head).symm.trans
    ((Equiv.sigmaCongrRight (fun v => Fintype.equivOfCardEq (hbal v))).trans
      (Equiv.sigmaFiberEquiv tail))

theorem successor_tail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (d : D) : tail (successor tail head hbal d) = head d := by
  exact (Fintype.equivOfCardEq (hbal (head d)) ⟨d,rfl⟩).property

/-- Some cycle class has nonzero weight whenever the total weight does. -/
theorem exists_cycle_nonzero (σ : Equiv.Perm D) (w : D → ℤ)
    (hw : ∑ d, w d ≠ 0) :
    ∃ d, (∑ e : D, if σ.SameCycle d e then w e else 0) ≠ 0 := by
  let Q := Quotient (Equiv.Perm.SameCycle.setoid σ)
  let q : D → Q := Quotient.mk _
  have hs : ∑ c : Q, (∑ e : D, if q e = c then w e else 0) = ∑ e, w e := by
    calc
      _ = ∑ e : D, ∑ c : Q, if q e = c then w e else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        exact (Finset.sum_ite_eq Finset.univ (q e) (fun _ => w e)).trans (ite_eq_left (Finset.mem_univ _))
  by_contra! h
  have hz : (∑ c : Q, ∑ e : D, if q e = c then w e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    obtain ⟨d,rfl⟩ := Quotient.exists_rep c
    convert h d using 1
    apply Finset.sum_congr rfl
    intro e _
    have he : q e = Quotient.mk (Equiv.Perm.SameCycle.setoid σ) d ↔ σ.SameCycle d e := by
      rw [Quotient.eq]
      exact Equiv.Perm.sameCycle_comm
    simp only [he]
  exact hw (hs.symm.trans hz)

theorem period_pos (σ : Equiv.Perm D) (d : D) : 0 < minimalPeriod σ d :=
  minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts d)

noncomputable def cycleEquiv (σ : Equiv.Perm D) (d : D) :
    Fin (minimalPeriod σ d) ≃ {e // σ.SameCycle d e} := by
  let f : Fin (minimalPeriod σ d) → {e // σ.SameCycle d e} := fun i =>
    ⟨σ^[i.val] d,by
      rw [←Equiv.Perm.coe_pow]
      exact Equiv.Perm.SameCycle.rfl.pow_right⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp (congrArg Subtype.val hij)
  · intro e
    obtain ⟨k,hk⟩ := e.property.exists_nat_pow_eq
    refine ⟨⟨k % minimalPeriod σ d,Nat.mod_lt _ (period_pos σ d)⟩,?_⟩
    apply Subtype.ext
    change σ^[k % minimalPeriod σ d] d = e.val
    rw [iterate_mod_minimalPeriod_eq,←Equiv.Perm.coe_pow]
    exact hk

def next {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩

/-- A closed trail has distinct edges and retains the nonzero marked crossing sum. -/
theorem exists_closed_trail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by
  let σ := successor tail head hbal
  obtain ⟨d,hd⟩ := exists_cycle_nonzero σ w hw
  let n := minimalPeriod σ d
  have hn : 0 < n := period_pos σ d
  let e : Fin n → D := fun i => σ^[i.val] d
  refine ⟨n,hn,e,?_,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp hij
  · intro i
    have he : e (next hn i) = σ (e i) := by
      change σ^[(i.val+1)%n] d = σ (σ^[i.val] d)
      rw [iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
    rw [he]
    exact successor_tail tail head hbal (e i)
  · have hs := (cycleEquiv σ d).sum_comp (fun z : {e // σ.SameCycle d e} => w z.val)
    have ht : (∑ z : {e // σ.SameCycle d e}, w z.val) =
        ∑ e : D, if σ.SameCycle d e then w e else 0 := by
      rw [←Finset.sum_filter]; exact (Finset.sum_subtype _ (by simp) w).symm
    rw [ht] at hs
    exact hs.symm ▸ hd

end FiniteTrails

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
abbrev Point := ℤ × ℤ
abbrev Direction := Fin 4

def tailOffset : Direction → Point := ![(0,0),(1,0),(1,1),(0,1)]
def headOffset : Direction → Point := ![(1,0),(1,1),(0,1),(0,0)]
def outward : Direction → Point := ![(0,-1),(1,0),(0,1),(-1,0)]

abbrev Boundary (X : Finset Point) := {e : Point × Direction // e.1 ∈ X ∧ e.1+outward e.2 ∉ X}

noncomputable instance (X : Finset Point) : Fintype (Boundary X) :=
  Fintype.ofInjective (fun e : Boundary X => (⟨e.val.1,e.property.1⟩,e.val.2) : Boundary X → X × Direction)
    (by intro e e' h; apply Subtype.ext; exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z : X × Direction => z.2) h))

def tail {X : Finset Point} (e : Boundary X) : Point := e.val.1+tailOffset e.val.2
def head {X : Finset Point} (e : Boundary X) : Point := e.val.1+headOffset e.val.2

noncomputable def atVertex (X : Finset Point) (v : Point) (offset : Direction → Point) :
    {e : Boundary X // e.val.1+offset e.val.2 = v} ≃
      {d : Direction // v-offset d ∈ X ∧ v-offset d+outward d ∉ X} where
  toFun e := ⟨e.val.val.2,by
    have he : e.val.val.1 = v-offset e.val.val.2 := eq_sub_iff_add_eq.mpr e.property
    rw [←he]
    exact e.val.property⟩
  invFun d := ⟨⟨(v-offset d.val,d.val),d.property⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (eq_sub_iff_add_eq.mpr e.property).symm
    · rfl
  right_inv d := by rfl

/-- At each dual vertex incoming and outgoing boundary degrees agree. -/
theorem balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  apply (Fintype.card_congr (atVertex X v headOffset)).trans
  apply Eq.trans _ (Fintype.card_congr (atVertex X v tailOffset)).symm
  simp only [Fintype.card_subtype,Finset.card_filter]
  simp only [Fin.sum_univ_succ,headOffset,tailOffset,outward,Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  have ha : v-(1,0)+(0,-1) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  have hb : v-(1,1)+(1,0) = v-(0,1) := by ext <;> simp
  have hc : v-(0,1)+(0,1) = v := sub_add_cancel _ _
  have hd : v+(-1,0) = v-(1,0) := by ext <;> simp [sub_eq_add_neg]
  have he : v+(0,-1) = v-(0,1) := by ext <;> simp [sub_eq_add_neg]
  have hf : v-(1,0)+(1,0) = v := sub_add_cancel _ _
  have hg : v-(1,1)+(0,1) = v-(1,0) := by ext <;> simp
  have hh : v-(0,1)+(-1,0) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  simp only [show ((0,0) : Point) = 0 from rfl,sub_zero,ha,hb,hc,hd,he,hf,hg,hh]
  by_cases h0 : v ∈ X <;> by_cases h1 : v-(1,0) ∈ X <;>
    by_cases h2 : v-(1,1) ∈ X <;> by_cases h3 : v-(0,1) ∈ X <;> simp [h0,h1,h2,h3]

theorem head_ne_tail {X : Finset Point} (e : Boundary X) : head e ≠ tail e := by
  intro h
  have he : headOffset e.val.2 = tailOffset e.val.2 := add_left_cancel h
  generalize hd : e.val.2 = d at he
  fin_cases d <;> simp [headOffset,tailOffset] at he

def opposite (d : Direction) : Direction := d+2

theorem opposite_opposite (d : Direction) : opposite (opposite d) = d := by
  fin_cases d <;> decide

theorem outward_opposite (d : Direction) : outward (opposite d) = -outward d := by
  fin_cases d <;> decide

theorem reverse_tail (d : Direction) : outward d+tailOffset (opposite d) = headOffset d := by
  fin_cases d <;> decide

theorem reverse_head (d : Direction) : outward d+headOffset (opposite d) = tailOffset d := by
  fin_cases d <;> decide

/-- Signed intersections with the positive horizontal ray; dual vertex (a,b)
represents the point (a-1/2,b-1/2). -/
def rayFlux (a b : Point) : ℤ :=
  (if a.2 = 0 ∧ b.2 = 1 ∧ 0 < a.1 then 1 else 0) -
  (if b.2 = 0 ∧ a.2 = 1 ∧ 0 < b.1 then 1 else 0)

theorem rayFlux_reverse (a b : Point) : rayFlux b a = -rayFlux a b := by
  unfold rayFlux
  ring

def sideFlux (cell : Point) (d : Direction) : ℤ :=
  rayFlux (cell+tailOffset d) (cell+headOffset d)

theorem sideFlux_reverse (cell : Point) (d : Direction) :
    sideFlux (cell+outward d) (opposite d) = -sideFlux cell d := by
  unfold sideFlux
  simp only [add_assoc,reverse_tail,reverse_head]
  exact rayFlux_reverse _ _

/-- The oriented boundary of one unit cell has ray intersection number one
exactly when it contains the ray's origin. No Jordan curve theorem is assumed. -/
theorem cell_flux (cell : Point) :
    (∑ d : Direction, sideFlux cell d) = if cell = (0,0) then 1 else 0 := by
  rcases cell with ⟨x,y⟩
  simp only [Fin.sum_univ_succ]
  simp [sideFlux,rayFlux,tailOffset,headOffset,Prod.ext_iff]
  split_ifs <;> omega

abbrev FullSide (X : Finset Point) := X × Direction

def isInternal {X : Finset Point} (e : FullSide X) : Prop := e.1.val+outward e.2 ∈ X

noncomputable def internalReverse (X : Finset Point) :
    {e : FullSide X // isInternal e} ≃ {e : FullSide X // isInternal e} := by
  let f : {e : FullSide X // isInternal e} → {e : FullSide X // isInternal e} :=
    fun e => ⟨(⟨e.val.1.val+outward e.val.2,e.property⟩,opposite e.val.2),by
      change e.val.1.val+outward e.val.2+outward (opposite e.val.2) ∈ X
      rw [outward_opposite,add_neg_cancel_right]
      exact e.val.1.property⟩
  have hf : Function.Involutive f := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact by simp [f,outward_opposite]
    · exact opposite_opposite _
  exact ⟨f,f,hf,hf⟩

theorem internal_flux_zero (X : Finset Point) :
    (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) = 0 := by
  let F : {e : FullSide X // isInternal e} → ℤ := fun e => sideFlux e.val.1.val e.val.2
  have hs := (internalReverse X).sum_comp F
  have he : (∑ e, F (internalReverse X e)) = -(∑ e, F e) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    exact sideFlux_reverse _ _
  rw [he] at hs
  dsimp [F] at hs
  omega

noncomputable def boundaryEquiv (X : Finset Point) :
    Boundary X ≃ {e : FullSide X // ¬isInternal e} where
  toFun e := ⟨(⟨e.val.1,e.property.1⟩,e.val.2),e.property.2⟩
  invFun e := ⟨(e.val.1.val,e.val.2),e.val.1.property,e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole finite boundary has nonzero positive-ray intersection number. -/
theorem boundary_flux (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by
  have hfull : (∑ e : FullSide X, sideFlux e.1.val e.2) = if (0,0) ∈ X then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    simp_rw [cell_flux]
    rw [←Finset.sum_subtype X (by simp) (fun cell => if cell = (0,0) then (1 : ℤ) else 0)]
    simp
  have hpart : (∑ e : {e : FullSide X // isInternal e}, sideFlux e.val.1.val e.val.2) +
      (∑ e : {e : FullSide X // ¬isInternal e}, sideFlux e.val.1.val e.val.2) =
      ∑ e : FullSide X, sideFlux e.1.val e.2 := by
    have h₁ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (isInternal (X := X)))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter isInternal ↔ isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    have h₂ := Finset.sum_subtype (F := inferInstance) (Finset.univ.filter (fun e : FullSide X => ¬isInternal e))
      (by simp : ∀ e : FullSide X, e ∈ Finset.univ.filter (fun e => ¬isInternal e) ↔ ¬isInternal e)
      (fun e : FullSide X => sideFlux e.1.val e.2)
    rw [←h₁,←h₂]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [internal_flux_zero,zero_add] at hpart
  rw [←hfull,←hpart]
  exact (boundaryEquiv X).sum_comp (fun e => sideFlux e.val.1.val e.val.2)

end PlanarBoundary

namespace PlanarBoundary
open Classical

def Neighbor (a b : Point) : Prop := ∃ d : Direction, b = a+outward d

theorem side_neighbor (cell : Point) (d : Direction) :
    Neighbor (cell+tailOffset d) (cell+headOffset d) := by
  refine ⟨d+1,?_⟩
  fin_cases d <;> ext <;> simp [headOffset,tailOffset,outward]

theorem head_neighbor {X : Finset Point} (e : Boundary X) : Neighbor (tail e) (head e) :=
  side_neighbor _ _

theorem neighbor_coord {a b : Point} (h : Neighbor a b) : |b.1-a.1| ≤ 1 := by
  obtain ⟨d,rfl⟩ := h
  fin_cases d <;> simp [outward]

def lineFlux (a b : Point) : ℤ := (if 1 ≤ b.2 then 1 else 0)-(if 1 ≤ a.2 then 1 else 0)

theorem rayFlux_eq_lineFlux {a b : Point} (h : Neighbor a b) :
    rayFlux a b = if 0 < a.1 then lineFlux a b else 0 := by
  obtain ⟨d,rfl⟩ := h
  rcases a with ⟨x,y⟩
  fin_cases d <;> simp [outward,rayFlux,lineFlux] <;> split_ifs <;> omega

theorem next_eq_rotate {n : ℕ} (hn : 0 < n) (i : Fin n) :
    FiniteTrails.next hn i = finRotate n i := by
  ext
  simp [FiniteTrails.next,finRotate_apply,Fin.add_def,Nat.add_mod_mod]

theorem lineFlux_sum_zero {n : ℕ} (hn : 0 < n) (v : Fin n → Point) :
    (∑ i, lineFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
  simp only [lineFlux,Finset.sum_sub_distrib,next_eq_rotate]
  exact sub_eq_zero.mpr (Equiv.sum_comp (finRotate n) (fun i => if 1 ≤ (v i).2 then (1 : ℤ) else 0))

/-- Nonzero positive-ray flux forces a crossing on each side of the vertical axis. -/
theorem two_sides {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)))
    (hw : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0) :
    (∃ i, 0 < (v i).1 ∧ rayFlux (v i) (v (FiniteTrails.next hn i)) ≠ 0) ∧
      ∃ j, (v j).1 ≤ 0 := by
  constructor
  · obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    refine ⟨i,?_,hi⟩
    by_contra! hh
    exact hi (by rw [rayFlux_eq_lineFlux (hedge i),ite_eq_right (not_lt.mpr hh)])
  · by_contra! hh
    have he : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) = 0 := by
      simp_rw [rayFlux_eq_lineFlux (hedge _),ite_eq_left (hh _)]
      exact lineFlux_sum_zero hn v
    exact hw he

/-- A coarse diameter bound adequate for the same Peierls argument. -/
theorem coordinate_diameter {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by
  let a : ℕ → ℤ := fun k => (v ⟨k%n,Nat.mod_lt _ hn⟩).1
  have hs (k : ℕ) : |a (k+1)-a k| ≤ 1 := by
    have he : FiniteTrails.next hn ⟨k%n,Nat.mod_lt _ hn⟩ =
        (⟨(k+1)%n,Nat.mod_lt _ hn⟩ : Fin n) := by
      ext
      exact Nat.mod_add_mod k n 1
    simpa only [he] using neighbor_coord (hedge ⟨k%n,Nat.mod_lt _ hn⟩)
  have hb (k : ℕ) : |a k-a 0| ≤ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        |a (k+1)-a 0| ≤ |a (k+1)-a k|+|a k-a 0| := abs_sub_le _ _ _
        _ ≤ 1+(k : ℤ) := add_le_add (hs k) ih
        _ = (k+1 : ℕ) := by omega
  have hi := (abs_le.mp (hb i.val)).2
  have hj := (abs_le.mp (hb j.val)).1
  dsimp [a] at hi hj
  simp only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt,Fin.eta] at hi hj
  have hin : (i.val : ℤ) < n := by exact_mod_cast i.isLt
  have hjn : (j.val : ℤ) < n := by exact_mod_cast j.isLt
  omega

/-- Every finite region containing zero contains an edge-simple closed boundary
trail with a positive-ray anchor of coordinate less than 2n. This deliberately
uses a harmless overcount rather than an unformalized Jordan theorem. -/
theorem exists_anchored_trail (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧
      (∀ i, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧
      ∃ i, 0 < (tail (e i)).1 ∧ (tail (e i)).1 < 2*(n : ℤ) ∧
        rayFlux (tail (e i)) (head (e i)) ≠ 0 := by
  have hw : (∑ e : Boundary X, rayFlux (tail e) (head e)) ≠ 0 := by
    rw [boundary_flux,ite_eq_left hX]
    norm_num
  obtain ⟨n,hn,e,he,hnext,hsum⟩ :=
    FiniteTrails.exists_closed_trail tail head (fun v => by
      simpa only [←Nat.card_eq_fintype_card] using balanced X v) (fun e => rayFlux (tail e) (head e)) hw
  let v : Fin n → Point := fun i => tail (e i)
  have hed : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i)) := by
    intro i
    dsimp [v]
    rw [hnext]
    exact head_neighbor _
  have hs : (∑ i, rayFlux (v i) (v (FiniteTrails.next hn i))) ≠ 0 := by
    simpa only [v,hnext] using hsum
  obtain ⟨⟨i,hi,hir⟩,j,hj⟩ := two_sides hn v hed hs
  have hd := coordinate_diameter hn v hed i j
  change (tail (e i)).1-(tail (e j)).1 < 2*(n : ℤ) at hd
  change (tail (e j)).1 ≤ 0 at hj
  refine ⟨n,hn,e,he,hnext,i,hi,by omega,?_⟩
  simpa only [v,hnext] using hir

end PlanarBoundary

namespace PlanarBoundary
open Classical

abbrev Code (n : ℕ) := Fin (2*n) × Bool × (Fin n → Direction)

def anchor {n : ℕ} (c : Code n) : Point := (c.1.val,if c.2.1 then 0 else 1)

def wordAt {n : ℕ} (w : Fin n → Direction) (k : ℕ) : Direction :=
  if hk : k < n then w ⟨k,hk⟩ else 0

def displacement (d : Direction) : Point := headOffset d-tailOffset d

def tracePosition {n : ℕ} (c : Code n) (k : ℕ) : Point :=
  anchor c+∑ j ∈ Finset.range k, displacement (wordAt c.2.2 j)

def traceSide {n : ℕ} (c : Code n) (i : Fin n) : Point × Direction :=
  (tracePosition c i.val-tailOffset (c.2.2 i),c.2.2 i)

theorem trace_succ {n : ℕ} (c : Code n) (k : ℕ) :
    tracePosition c (k+1) = tracePosition c k+displacement (wordAt c.2.2 k) := by
  simp only [tracePosition,Finset.sum_range_succ,add_assoc]

theorem trace_reconstruct {n : ℕ} (hn : 0 < n) {X : Finset Point}
    (e : Fin n → Boundary X) (he : ∀ i, tail (e (FiniteTrails.next hn i)) = head (e i))
    (c : Code n) (hanchor : anchor c = tail (e ⟨0,hn⟩))
    (hword : ∀ i, c.2.2 i = (e i).val.2) :
    ∀ i, traceSide c i = (e i).val := by
  have ht (k : ℕ) (hk : k < n) : tracePosition c k = tail (e ⟨k,hk⟩) := by
    induction k with
    | zero => simpa only [tracePosition,Finset.range_zero,Finset.sum_empty,add_zero] using hanchor
    | succ k ih =>
      have hkn : k < n := Nat.lt_trans (Nat.lt_succ_self _) hk
      rw [trace_succ,ih hkn]
      simp only [wordAt,dite_eq_left hkn,hword,displacement]
      have hx := he ⟨k,hkn⟩
      have hnxt : FiniteTrails.next hn ⟨k,hkn⟩ = (⟨k+1,hk⟩ : Fin n) := by
        ext
        exact Nat.mod_eq_of_lt hk
      rw [hnxt] at hx
      rw [hx]
      simp only [tail,head]
      abel
  intro i
  rw [traceSide,ht,hword]
  apply Prod.ext
  · exact add_sub_cancel_right _ _
  · rfl

def shiftIndex {n : ℕ} (hn : 0 < n) (a i : Fin n) : Fin n :=
  ⟨(i.val+a.val)%n,Nat.mod_lt _ hn⟩

theorem shiftIndex_injective {n : ℕ} (hn : 0 < n) (a : Fin n) :
    Function.Injective (shiftIndex hn a) := by
  intro i j he
  have h : (i+a : Fin n) = j+a := by
    apply Fin.ext
    exact congrArg Fin.val he
  exact add_right_cancel h

theorem shiftIndex_next {n : ℕ} (hn : 0 < n) (a i : Fin n) :
    shiftIndex hn a (FiniteTrails.next hn i) = FiniteTrails.next hn (shiftIndex hn a i) := by
  ext
  simp only [shiftIndex,FiniteTrails.next,Nat.mod_add_mod]
  congr 1
  omega

theorem rayFlux_ne_zero_height {a b : Point} (h : rayFlux a b ≠ 0) : a.2 = 0 ∨ a.2 = 1 := by
  unfold rayFlux at h
  split_ifs at h <;> aesop

/-- The finite deterministic code family has at most 4n4^n members. -/
theorem card_code (n : ℕ) : Fintype.card (Code n) = 4*n*4^n := by
  simp only [Code,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_fun,Direction]
  ring

/-- Every actual boundary supplies one of these finitely encoded trails. -/
theorem exists_boundary_code (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ _hn : 0 < n, ∃ c : Code n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧ ∀ i, traceSide c i = (e i).val := by
  obtain ⟨n,hn,e,he,hnext,a,ha0,haN,ha⟩ := exists_anchored_trail X hX
  let e' : Fin n → Boundary X := fun i => e (shiftIndex hn a i)
  have he' : Function.Injective e' := he.comp (shiftIndex_injective hn a)
  have hs' (i : Fin n) : tail (e' (FiniteTrails.next hn i)) = head (e' i) := by
    dsimp [e']
    rw [shiftIndex_next,hnext]
  have hz : e' ⟨0,hn⟩ = e a := by
    dsimp [e']
    congr 1
    apply Fin.ext
    simpa only [shiftIndex,Nat.zero_add] using Nat.mod_eq_of_lt a.isLt
  let x := (tail (e a)).1
  have hx0 : 0 ≤ x := le_of_lt ha0
  have hxn : x.toNat < 2*n := by omega
  obtain hy | hy := rayFlux_ne_zero_height ha
  · let c : Code n := (⟨x.toNat,hxn⟩,true,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm
  · let c : Code n := (⟨x.toNat,hxn⟩,false,fun i => (e' i).val.2)
    refine ⟨n,hn,c,e',he',trace_reconstruct hn e' hs' c ?_ (fun _ => rfl)⟩
    rw [hz]
    apply Prod.ext
    · exact Int.toNat_of_nonneg hx0
    · exact hy.symm

end PlanarBoundary

end OAI
end
end

section
section
namespace OAI


open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Exact greedy constants used in the shell trials and contour estimate. -/
namespace GreedyPacking
open Classical

variable {α : Type uAlpha}

/-- Greedily deleting at most M conflicts loses at most M elements per choice. -/
theorem exists_packing (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M : ℕ) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M) :
    ∃ s : Finset α, s ⊆ t ∧ (s : Set α).Pairwise (fun a b => ¬R a b) ∧ t.card ≤ M*s.card := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
    by_cases ht : t = ∅
    · subst t
      exact ⟨∅,by simp,by simp,by simp⟩
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr ht
    let u := t.filter (fun b => ¬R a b)
    have hu : u ⊆ t := Finset.filter_subset _ _
    have hau : a ∉ u := by simp [u,hrefl a ha]
    have hut : u ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hu,by intro h; exact hau (h.symm ▸ ha)⟩
    obtain ⟨s,hs,hpair,hcard⟩ := ih u hut
      (fun b hb => hrefl b (hu hb))
      (fun b hb c hc h => hsym b (hu hb) c (hu hc) h)
      (fun b hb => le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hu)) (hM b (hu hb)))
    refine ⟨insert a s,Finset.insert_subset ha (hs.trans hu),?_,?_⟩
    · simp only [Finset.coe_insert]
      rw [Set.pairwise_insert]
      refine ⟨hpair,?_⟩
      intro b hb _
      exact ⟨(Finset.mem_filter.mp (hs hb)).2,
        fun h => (Finset.mem_filter.mp (hs hb)).2 (hsym b (hu (hs hb)) a ha h)⟩
    · have has : a ∉ s := fun h => hau (hs h)
      rw [Finset.card_insert_of_notMem has]
      have he : (t.filter (R a)).card+u.card = t.card := by
        exact Finset.card_filter_add_card_filter_not (s := t) (R a)
      have hm := hM a ha
      nlinarith

/-- The prescribed K choices exist once there are K M candidates. -/
theorem exists_packing_card (t : Finset α) (R : α → α → Prop)
    (hrefl : ∀ a ∈ t, R a a) (hsym : ∀ a ∈ t, ∀ b ∈ t, R a b → R b a)
    (M K : ℕ) (hM0 : 0 < M) (hM : ∀ a ∈ t, (t.filter (R a)).card ≤ M)
    (ht : K*M ≤ t.card) :
    ∃ s : Finset α, s ⊆ t ∧ s.card = K ∧ (s : Set α).Pairwise (fun a b => ¬R a b) := by
  obtain ⟨s,hs,hpair,hcard⟩ := exists_packing t R hrefl hsym M hM
  have hk : K ≤ s.card := by nlinarith
  obtain ⟨u,hu,huc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨u,hu.trans hs,huc,hpair.mono hu⟩

end GreedyPacking

namespace FiniteMatching
open Classical
variable {E : Type uE} {V : Type uV} [Fintype E]

noncomputable def incident (a b : E → V) (v : V) : Finset E :=
  Finset.univ.filter (fun e => a e = v ∨ b e = v)

def conflict (a b : E → V) (e f : E) : Prop :=
  a e = a f ∨ a e = b f ∨ b e = a f ∨ b e = b f

omit [Fintype E] in
theorem conflict_refl (a b : E → V) (e : E) : conflict a b e e := Or.inl rfl

omit [Fintype E] in
theorem conflict_symm (a b : E → V) {e f : E} : conflict a b e f → conflict a b f e := by
  unfold conflict
  aesop

theorem conflict_card (a b : E → V)
    (hdeg : ∀ v, (incident a b v).card ≤ 4) (e : E) :
    (Finset.univ.filter (conflict a b e)).card ≤ 7 := by
  have heq : Finset.univ.filter (conflict a b e) = incident a b (a e) ∪ incident a b (b e) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,incident,conflict,
      Finset.mem_filter,Finset.mem_univ,true_and]
    aesop
  rw [heq]
  have hi : e ∈ incident a b (a e) ∩ incident a b (b e) := by simp [incident]
  have hpos := Finset.card_pos.mpr ⟨e,hi⟩
  have he := Finset.card_union_add_card_inter (incident a b (a e)) (incident a b (b e))
  have ha := hdeg (a e)
  have hb := hdeg (b e)
  omega

theorem exists_matching (a b : E → V) (hdeg : ∀ v, (incident a b v).card ≤ 4) :
    ∃ s : Finset E, (s : Set E).Pairwise (fun e f => ¬conflict a b e f) ∧
      Fintype.card E ≤ 7*s.card := by
  obtain ⟨s,_,hp,hc⟩ := GreedyPacking.exists_packing Finset.univ (conflict a b)
    (fun e _ => conflict_refl a b e) (fun _ _ _ _ => conflict_symm a b)
    7 (fun e _ => conflict_card a b hdeg e)
  exact ⟨s,hp,by simpa only [Finset.card_univ] using hc⟩

/- Choosing either endpoint of each edge of a matching gives distinct vertices. -/
omit [Fintype E] in
theorem endpoint_injective (a b : E → V) (s : Finset E)
    (hp : (s : Set E).Pairwise (fun e f => ¬conflict a b e f)) (choice : s → Bool) :
    Function.Injective (fun e : s => if choice e then a e.val else b e.val) := by
  intro e f hef
  by_contra hne
  have hn : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hc := hp e.property f.property hn
  cases he : choice e <;> cases hf : choice f <;> simp only [he,hf,Bool.false_eq_true,
    ite_false,ite_true] at hef
  · exact hc (Or.inr (Or.inr (Or.inr hef)))
  · exact hc (Or.inr (Or.inr (Or.inl hef)))
  · exact hc (Or.inr (Or.inl hef))
  · exact hc (Or.inl hef)

end FiniteMatching

namespace PlanarBoundary
open Classical

def primalInside {X : Finset Point} (e : Boundary X) : Point := e.val.1
def primalOutside {X : Finset Point} (e : Boundary X) : Point := e.val.1+outward e.val.2

/-- Boundary edges incident to a fixed primal vertex have at most four possibilities. -/
theorem boundary_degree (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // primalInside e = v ∨ primalOutside e = v} ≤ 4 := by
  let f : {e : Boundary X // primalInside e = v ∨ primalOutside e = v} → Direction :=
    fun e => e.val.val.2
  have hinj : Function.Injective f := by
    intro e g he
    have hd : e.val.val.2 = g.val.val.2 := he
    have hc : e.val.val.1 = g.val.val.1 := by
      by_cases hv : v ∈ X
      · have hve : primalInside e.val = v := e.property.resolve_right
          (by intro h; apply e.val.property.2; change primalOutside e.val ∈ X; rwa [h])
        have hvg : primalInside g.val = v := g.property.resolve_right
          (by intro h; apply g.val.property.2; change primalOutside g.val ∈ X; rwa [h])
        exact hve.trans hvg.symm
      · have hve : primalOutside e.val = v := e.property.resolve_left
          (fun h => hv (h ▸ e.val.property.1))
        have hvg : primalOutside g.val = v := g.property.resolve_left
          (fun h => hv (h ▸ g.val.property.1))
        have hh := hve.trans hvg.symm
        change e.val.val.1+outward e.val.val.2 = g.val.val.1+outward g.val.val.2 at hh
        rw [hd] at hh
        exact add_right_cancel hh
    exact Subtype.ext (Subtype.ext (Prod.ext hc hd))
  exact (Fintype.card_le_of_injective f hinj).trans_eq (Fintype.card_fin 4)

def Valid {n : ℕ} (c : Code n) : Prop :=
  ∃ X : Finset Point, ∃ e : Fin n → Boundary X, Function.Injective e ∧
    ∀ i, traceSide c i = (e i).val

def inner {n : ℕ} (c : Code n) (i : Fin n) : Point := (traceSide c i).1
def outer {n : ℕ} (c : Code n) (i : Fin n) : Point :=
  (traceSide c i).1+outward (traceSide c i).2

theorem code_degree {n : ℕ} (c : Code n) (hc : Valid c) (v : Point) :
    (FiniteMatching.incident (inner c) (outer c) v).card ≤ 4 := by
  obtain ⟨X,e,hinj,he⟩ := hc
  let f : {i : Fin n // inner c i = v ∨ outer c i = v} →
      {e : Boundary X // primalInside e = v ∨ primalOutside e = v} := fun i =>
    ⟨e i.val,by simpa only [primalInside,primalOutside,inner,outer,he] using i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hinj (congrArg Subtype.val hij)
  have hh := (Fintype.card_le_of_injective f hf).trans (boundary_degree X v)
  have heq : (FiniteMatching.incident (inner c) (outer c) v).card =
      Fintype.card {i : Fin n // inner c i = v ∨ outer c i = v} := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext i
    simp only [FiniteMatching.incident, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [heq]
  exact hh

theorem exists_code_matching {n : ℕ} (c : Code n) (hc : Valid c) :
    ∃ s : Finset (Fin n),
      (s : Set (Fin n)).Pairwise (fun i j => ¬FiniteMatching.conflict (inner c) (outer c) i j) ∧
      n ≤ 7*s.card := by
  simpa only [Fintype.card_fin] using FiniteMatching.exists_matching _ _ (code_degree c hc)

end PlanarBoundary

end OAI
end
end

section
section
namespace OAI


open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def blocked {n : ℕ} (Bad : Point → Set Ω) (c : Code n) : Set Ω :=
  {ω | ∀ i, ω ∈ Bad (inner c i) ∨ ω ∈ Bad (outer c i)}

/-- Matching and endpoint union bound; the bad vertices may be arbitrarily dependent. -/
theorem blocked_bound {n : ℕ} (Bad : Point → Set Ω) (c : Code n) (hc : Valid c)
    {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) :
    μ.real (blocked Bad c) ≤ (2*f)^((n : ℝ)/7) := by
  obtain ⟨s,hpair,hsize⟩ := exists_code_matching c hc
  let choose (η : s → Bool) (i : s) := if η i then inner c i.val else outer c i.val
  let E (η : s → Bool) : Set Ω := {ω | ∀ i : s, ω ∈ Bad (choose η i)}
  have hE (η : s → Bool) : μ.real (E η) ≤ f^s.card := by
    let t : Finset Point := Finset.univ.image (choose η)
    have hinj : Function.Injective (choose η) :=
      FiniteMatching.endpoint_injective _ _ s hpair η
    have ht : t.card = s.card := by
      rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
    have he : E η = {ω | ∀ v ∈ t, ω ∈ Bad v} := by
      ext ω
      constructor
      · intro h v hv
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
        exact h i
      · intro h i
        exact h _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [he,←ht]
    exact hbad t
  have hcover : blocked Bad c ⊆ ⋃ η, E η := by
    intro ω hω
    let η : s → Bool := fun i => if ω ∈ Bad (inner c i.val) then true else false
    refine Set.mem_iUnion.mpr ⟨η,?_⟩
    intro i
    by_cases hi : ω ∈ Bad (inner c i.val)
    · simp only [choose,η,hi,ite_true]
    · simpa only [choose,η,hi,ite_false,Bool.false_eq_true] using (hω i.val).resolve_left hi
  have hbound : μ.real (blocked Bad c) ≤ (2*f)^s.card := by
    calc
      _ ≤ μ.real (⋃ η, E η) := measureReal_mono hcover
      _ ≤ ∑ η, μ.real (E η) := measureReal_iUnion_fintype_le E
      _ ≤ ∑ _η : s → Bool, f^s.card := Finset.sum_le_sum (fun η _ => hE η)
      _ = (2*f)^s.card := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
          Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow]
  apply hbound.trans
  rw [←Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge (by positivity) hf1
  have hs : (n : ℝ) ≤ 7*s.card := by exact_mod_cast hsize
  linarith

/-- Codes arising from actual boundaries are the only candidates needed. -/
def candidate {n : ℕ} (Bad : Point → Set Ω) (c : {c : Code n // Valid c}) : Set Ω :=
  blocked Bad c.val

theorem candidates_bound (Bad : Point → Set Ω) {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) (n : ℕ) :
    μ.real (⋃ c : {c : Code n // Valid c}, candidate Bad c) ≤
      4*(n : ℝ)*4^n*(2*f)^((n : ℝ)/7) := by
  calc
    _ ≤ ∑ c : {c : Code n // Valid c}, μ.real (candidate Bad c) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : {c : Code n // Valid c}, (2*f)^((n : ℝ)/7) :=
      Finset.sum_le_sum (fun c _ => blocked_bound μ Bad c.val c.property hf0 hf1 hbad)
    _ = (Fintype.card {c : Code n // Valid c} : ℝ)*(2*f)^((n : ℝ)/7) := by simp
    _ ≤ (Fintype.card (Code n) : ℝ)*(2*f)^((n : ℝ)/7) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Fintype.card_subtype_le (fun c : Code n => Valid c)
      · positivity
    _ = _ := by rw [card_code]; push_cast; ring

/-- A summable real upper bound for countably many events bounds their union. -/
theorem union_bound (A : ℕ → Set Ω) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) (hA : ∀ n, μ.real (A n) ≤ g n) :
    μ.real (⋃ n, A n) ≤ ∑' n, g n := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (tsum_nonneg hg0)).mp
  rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  apply (measure_iUnion_le A).trans
  apply ENNReal.tsum_le_tsum
  intro n
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hg0 n)).mpr (hA n)

/-- Exact numerical budget for the benign overcount of encoded trails. -/
theorem encoded_budget_hasSum :
    HasSum (fun n : ℕ => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7)) (25/144 : ℝ) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(4/100 : ℝ)‖ < 1)).mul_left 4
  have he (n : ℕ) : 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7) =
      4*((n : ℝ)*(4/100 : ℝ)^n) := by
    rw [CriticalScales.contour_power]
    have hp : (4/100 : ℝ)^n = 4^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hp]
    ring
  simp_rw [he]
  have hz : 4*((4/100 : ℝ)/(1-4/100)^2) = 25/144 := by norm_num
  rw [hz] at h
  exact h

omit [MeasurableSpace Ω] in
/-- The main contour inclusion, without conditioning on a random boundary. -/
theorem finite_good_subset (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d)) :
    {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ⊆
      ⋃ n, ⋃ c : {c : Code n // Valid c}, candidate Bad c := by
  intro ω hω
  let X := hω.1.toFinset
  have hX : (0,0) ∈ X := by simpa only [X,Set.Finite.mem_toFinset] using hω.2
  obtain ⟨n,_,c,e,hinj,he⟩ := exists_boundary_code X hX
  refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨c,X,e,hinj,he⟩,?_⟩⟩
  intro i
  right
  change ω ∈ Bad ((traceSide c i).1+outward (traceSide c i).2)
  rw [he]
  apply houtside ω hω.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.1
  · simpa only [X,Set.Finite.mem_toFinset] using (e i).property.2

theorem finite_good_bound (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d))
    (hbad : ∀ s : Finset Point,
      μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ CriticalScales.contourError^s.card) :
    μ.real {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ≤ 25/144 := by
  apply (measureReal_mono (finite_good_subset Good Bad houtside)).trans
  have h := union_bound μ (fun n => ⋃ c : {c : Code n // Valid c}, candidate Bad c)
    (fun n => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7))
    (fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [CriticalScales.contourError_pos]) _)) encoded_budget_hasSum.summable
    (candidates_bound μ Bad CriticalScales.contourError_pos
      (by linarith [CriticalScales.contourError_lt_half]) hbad)
  rwa [encoded_budget_hasSum.tsum_eq] at h

end PlanarBoundary

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Coarse
abbrev Point := PlanarBoundary.Point
abbrev Direction := PlanarBoundary.Direction
abbrev outward := PlanarBoundary.outward

def center (r : ℕ) (v : Point) : Vertex := ![(20*(r:ℤ)+1)*v.1,(20*(r:ℤ)+1)*v.2,0]
def Q (r : ℕ) (v : Point) : Box := Box.cube (center r v) (10*r)
def B (r : ℕ) (v : Point) : Box := Box.cube (center r v) (4*r)
def PairRegion (r : ℕ) (v x : Point) : Set Vertex := {y | (Q r v).Contains y ∨ (Q r x).Contains y}

@[simp] theorem center_zero (r : ℕ) : center r 0 = 0 := by ext i; fin_cases i <;> simp [center]

theorem cube_unique (r : ℕ) {v w : Point} {x : Vertex}
    (hv : (Q r v).Contains x) (hw : (Q r w).Contains x) : v = w := by
  have hg (a b t : ℤ) (h0 : (20*(r:ℤ)+1)*a-(10*r:ℕ) ≤ t)
      (h1 : t ≤ (20*(r:ℤ)+1)*a+(10*r:ℕ))
      (h2 : (20*(r:ℤ)+1)*b-(10*r:ℕ) ≤ t)
      (h3 : t ≤ (20*(r:ℤ)+1)*b+(10*r:ℕ)) : a = b := by
    push_cast at h0 h1 h2 h3
    have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
    by_contra h
    rcases lt_or_gt_of_ne h with hh|hh
    · have : a+1 ≤ b := by omega
      nlinarith
    · have : b+1 ≤ a := by omega
      nlinarith
  apply Prod.ext
  · exact hg v.1 w.1 (x 0) (hv 0).1 (hv 0).2 (hw 0).1 (hw 0).2
  · exact hg v.2 w.2 (x 1) (hv 1).1 (hv 1).2 (hw 1).1 (hw 1).2

theorem Q_disjoint (r : ℕ) {v w : Point} (h : v ≠ w) : Disjoint (Q r v).vertices (Q r w).vertices := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h (cube_unique r ((Box.mem_vertices _ _).mp hx) ((Box.mem_vertices _ _).mp hy))

theorem B_subset_Q (r : ℕ) (v : Point) : ∀ x, (B r v).Contains x → (Q r v).Contains x := by
  intro x hx
  apply Box.contains_cube_iff.mpr
  exact cube_mono (center r v) (by omega) (Box.contains_cube_iff.mp hx)

theorem zero_in_Q (r : ℕ) : (Q r 0).Contains 0 := by
  rw [Q,center_zero]
  exact Box.center_mem_cube _ _

theorem zero_outside_pair (r : ℕ) {v w : Point} (hv : v ≠ 0) (hw : w ≠ 0) :
    (0:Vertex) ∉ PairRegion r v w := by
  rintro (h|h)
  · exact hv (cube_unique r h (zero_in_Q r))
  · exact hw (cube_unique r h (zero_in_Q r))

noncomputable def interface (r : ℕ) (v w : Point) : Finset Bond :=
  (((Q r v).vertices ∪ (Q r w).vertices) ×ˢ Finset.univ).filter
    (fun e => ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)))

@[simp] theorem mem_interface (r : ℕ) (v w : Point) (e : Bond) : e ∈ interface r v w ↔
    ((Q r v).Contains e.1 ∧ (Q r w).Contains (step e.1 e.2)) ∨
      ((Q r w).Contains e.1 ∧ (Q r v).Contains (step e.1 e.2)) := by
  simp only [interface,Finset.mem_filter,Finset.mem_product,Finset.mem_union,
    Box.mem_vertices,Finset.mem_univ,and_true]
  exact ⟨fun h => h.2,fun h => ⟨h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),h⟩⟩

theorem interface_comm (r : ℕ) (v w : Point) : interface r v w = interface r w v := by
  ext e
  simp only [mem_interface,or_comm]

theorem interface_eq_endpoints (r : ℕ) {v w a b : Point} {e : Bond}
    (h : e ∈ interface r v w) (h' : e ∈ interface r a b) :
    (v = a ∧ w = b) ∨ (v = b ∧ w = a) := by
  rw [mem_interface] at h h'
  rcases h with h|h <;> rcases h' with h'|h'
  · exact Or.inl ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.1 h'.1,cube_unique r h.2 h'.2⟩
  · exact Or.inr ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩
  · exact Or.inl ⟨cube_unique r h.2 h'.2,cube_unique r h.1 h'.1⟩

theorem internal_not_interface (r : ℕ) {u v w : Point} (hvw : v ≠ w) :
    Disjoint (Q r u).bonds (interface r v w) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hi
  have hh := (Box.mem_bonds _ _).mp he
  rw [mem_interface] at hi
  rcases hi with hi|hi
  · exact hvw ((cube_unique r hi.1 hh.1).trans (cube_unique r hh.2 hi.2))
  · exact hvw ((cube_unique r hi.2 hh.2).trans (cube_unique r hh.1 hi.1))

theorem internal_pair_bond (r : ℕ) (v w : Point) (e : Bond) :
    Model.Internal .bond (PairRegion r v w) e ↔
      e ∈ (Q r v).bonds ∪ (Q r w).bonds ∪ interface r v w := by
  simp only [Model.Internal,PairRegion,Set.mem_ofPred_eq,Finset.mem_union,Box.mem_bonds,mem_interface]
  tauto

def frame (r : ℕ) (v : Point) (d : Direction) : SignedSymmetry where
  perm := if d = 0 ∨ d = 2 then Equiv.swap 0 1 else Equiv.refl _
  signs := fun i => if d = 0 then decide (i ≠ 1) else if d = 3 then decide (i ≠ 0) else true
  shift := center r v

@[simp] theorem frame_zero (r : ℕ) (v : Point) (d : Direction) : (frame r v d).vertex 0 = center r v := by
  ext i
  simp [frame,SignedSymmetry.vertex]

@[simp] theorem frame_next (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex (LatticeRelay.axisCenter (20*(r:ℤ)+1)) = center r (v+outward d) := by
  ext i
  fin_cases d <;> fin_cases i <;> simp [frame,SignedSymmetry.vertex,LatticeRelay.axisCenter,
    center,outward,PlanarBoundary.outward,Equiv.swap_apply_def] <;> ring

theorem relay_cube_eq (c : Vertex) (n : ℕ) : LatticeRelay.Cube c n = cube c n := by
  ext x
  rw [mem_cube]
  constructor <;> intro h i
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ) at hh
    rw [abs_le] at hh
    omega
  · have hh := h i
    change |x i-c i| ≤ (n:ℤ)
    rw [abs_le]
    omega

theorem image_cube (S : SignedSymmetry) (c : Vertex) (n : ℕ) : S.vertex '' cube c n = cube (S.vertex c) n := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (S.cube_map c y n).mp hy
  · intro hx
    exact ⟨S.vertex.symm x,(S.cube_map c _ n).mpr (by simpa only [Equiv.apply_symm_apply] using hx),S.vertex.apply_symm_apply x⟩

theorem prism_eq_cubes (r : ℕ) : LatticeRelay.Prism r =
    LatticeRelay.Cube 0 (10*r) ∪ LatticeRelay.Cube (LatticeRelay.axisCenter (20*(r:ℤ)+1)) (10*r) := by
  ext x
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  constructor
  · intro hx
    by_cases h : x 0 ≤ 10*(r:ℤ)
    · left
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-0| ≤ _
        rw [sub_zero,abs_le]
        exact ⟨hx.1,h⟩
      · simpa only [Pi.zero_apply,sub_zero] using hx.2.2 i hi
    · right
      intro i
      by_cases hi : i = 0
      · subst i
        change |x 0-(20*(r:ℤ)+1)| ≤ _
        change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ)
        rw [abs_le]
        have hh := hx.2.1
        omega
      · simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx.2.2 i hi
  · rintro (hx|hx)
    · have hh := hx 0
      change |x 0-0| ≤ 10*(r:ℤ) at hh
      rw [sub_zero,abs_le] at hh
      refine ⟨hh.1,by omega,?_⟩
      intro i _
      simpa only [Pi.zero_apply,sub_zero] using hx i
    · have hh := hx 0
      change |x 0-(20*(r:ℤ)+1)| ≤ 10*(r:ℤ) at hh
      rw [abs_le] at hh
      refine ⟨by omega,by omega,?_⟩
      intro i hi
      simpa only [LatticeRelay.axisCenter,hi,ite_false,sub_zero] using hx i

theorem frame_prism (r : ℕ) (v : Point) (d : Direction) :
    (frame r v d).vertex '' LatticeRelay.Prism r = PairRegion r v (v+outward d) := by
  rw [prism_eq_cubes,Set.image_union]
  have he : (10:ℤ)*r = (10*r:ℕ) := by push_cast; rfl
  rw [he,relay_cube_eq,relay_cube_eq,image_cube,image_cube,frame_zero,frame_next]
  ext x
  simp only [Set.mem_union,PairRegion,Set.mem_ofPred_eq,Q,Box.contains_cube_iff]

theorem neighboring_relay {model : Model} (s : ScaleData model) (G : LatticeGraph)
    (p : model.Bit → Set.Icc (0:ℝ) 1) (v : Point) (d : Direction)
    (hG : G.ContainsSet (PairRegion s.r v (v+outward d)))
    (hp : model.UniformOn p s.q (PairRegion s.r v (v+outward d)))
    (o : G.Node) (ho : o.1 ∉ PairRegion s.r v (v+outward d)) :
    (ProductCylinder.law p).real {ω | G.Meets model ω o {x | (B s.r v).Contains x} ∧
      ¬G.Meets model ω o {x | (B s.r (v+outward d)).Contains x}} ≤ 13*s.η := by
  have h := s.relay_in_frame G p (frame s.r v d) (by rwa [frame_prism]) (by rwa [frame_prism]) o
    (by rwa [frame_prism])
  simpa only [frame_zero,frame_next,B,Box.contains_cube_iff,Set.ofPred_mem_eq] using h
end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

def Subgraph (G H : LatticeGraph) : Prop := G.vertices ⊆ H.vertices ∧ G.edges ⊆ H.edges

theorem conn_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {x y : G.Node} (hc : G.Conn m ω x y) :
    H.Conn m ω ⟨x.1,h.1 x.2⟩ ⟨y.1,h.1 y.2⟩ := by
  rw [G.conn_iff] at hc
  rw [H.conn_iff]
  refine ⟨?_,hc.2.lift (fun z : G.Node => (⟨z.1,h.1 z.2⟩ : H.Node)) ?_⟩
  · cases m <;> exact hc.1
  · intro a b hab
    cases m
    · obtain ⟨e,he,hi,ho⟩ := hab
      exact ⟨e,h.2 he,hi,ho⟩
    · obtain ⟨⟨e,he,hi⟩,ha,hb⟩ := hab
      exact ⟨⟨e,h.2 he,hi⟩,ha,hb⟩

theorem meets_inclusion {G H : LatticeGraph} (h : G.Subgraph H) (m : Model) {ω : m.Config}
    {o : G.Node} {T : Set Vertex} (hc : G.Meets m ω o T) :
    H.Meets m ω ⟨o.1,h.1 o.2⟩ T := by
  obtain ⟨y,hy,hc⟩ := hc
  exact ⟨⟨y.1,h.1 y.2⟩,hy,conn_inclusion h m hc⟩

noncomputable def ofBox (B : Box) : LatticeGraph where
  vertices := B.vertices
  edges := B.bonds
  left_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).1
  right_mem := fun _ he => (B.mem_vertices _).mpr ((B.mem_bonds _).mp he).2

@[simp] theorem ofBox_contains (B : Box) : (ofBox B).ContainsBox B := ⟨fun _ h => h,fun _ h => h⟩
end LatticeGraph

namespace Coarse
noncomputable def linkBits : (m : Model) → ℕ → Point → Point → Finset m.Bit
  | .bond,r,v,w => interface r v w
  | .site,_,_,_ => ∅
noncomputable def block (m : Model) (r : ℕ) (v parent : Point) : Finset m.Bit :=
  (Q r v).bits m ∪ linkBits m r v parent
noncomputable def rootBits (m : Model) (r : ℕ) : Finset m.Bit :=
  (Q r 0).bits m ∪ Finset.univ.biUnion (fun d : Direction => linkBits m r 0 (outward d))
noncomputable def exposed (m : Model) (r : ℕ) (D : Finset Point) : Finset m.Bit :=
  rootBits m r ∪ D.biUnion (fun v => (Q r v).bits m) ∪
    (D ×ˢ D).biUnion (fun e => linkBits m r e.1 e.2)

theorem bits_disjoint (m : Model) (r : ℕ) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r v).bits m) ((Q r w).bits m) := by
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    exact h (cube_unique r ((Box.mem_bonds _ _).mp he).1 ((Box.mem_bonds _ _).mp hf).1)
  · exact Q_disjoint r h

theorem bits_link_disjoint (m : Model) (r : ℕ) (u : Point) {v w : Point} (h : v ≠ w) :
    Disjoint ((Q r u).bits m) (linkBits m r v w) := by
  cases m
  · exact internal_not_interface r h
  · exact Finset.disjoint_empty_right _

theorem block_disjoint (m : Model) (r : ℕ) {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (hw : w ∉ D) (ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block m r v a) (block m r w b) := by
  have hva : v ≠ a := fun h => hv (h ▸ ha)
  have hwb : w ≠ b := fun h => hw (h ▸ hb)
  rw [block,block,Finset.disjoint_union_left,Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  refine ⟨⟨bits_disjoint m r hvw,bits_link_disjoint m r v hwb⟩,
    ⟨(bits_link_disjoint m r w hva).symm,?_⟩⟩
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he hf
    rcases interface_eq_endpoints r he hf with h|h
    · exact hvw h.1
    · exact hv (h.1 ▸ hb)
  · exact Finset.disjoint_empty_left _

theorem block_subset_exposed_insert (m : Model) (r : ℕ) {D : Finset Point}
    {v a : Point} (ha : a ∈ D) : block m r v a ⊆ exposed m r (insert v D) := by
  intro e he
  rw [block,Finset.mem_union] at he
  rcases he with he|he
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨v,Finset.mem_insert_self _ _,he⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨(v,a),Finset.mem_product.mpr ⟨Finset.mem_insert_self _ _,Finset.mem_insert_of_mem ha⟩,he⟩)

theorem exposed_mono (m : Model) (r : ℕ) {D D' : Finset Point} (h : D ⊆ D') :
    exposed m r D ⊆ exposed m r D' := by
  intro e he
  simp only [exposed,Finset.mem_union,Finset.mem_biUnion,Finset.mem_product] at he ⊢
  rcases he with (he|⟨v,hv,he⟩)|⟨⟨v,w⟩,⟨hv,hw⟩,he⟩
  · exact Or.inl (Or.inl he)
  · exact Or.inl (Or.inr ⟨v,h hv,he⟩)
  · exact Or.inr ⟨(v,w),⟨h hv,h hw⟩,he⟩

theorem internal_pair_not_exposed (m : Model) (r : ℕ) {D : Finset Point}
    (h0 : 0 ∈ D) {v w : Point} (hv : v ∉ D) (hw : w ∉ D) {e : m.Bit}
    (he : m.Internal (PairRegion r v w) e) : e ∉ exposed m r D := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ h0)
  have hw0 : w ≠ 0 := fun h => hw (h ▸ h0)
  cases m
  · change e ∉ _
    rw [internal_pair_bond] at he
    simp only [Finset.mem_union] at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Finset.mem_product,Finset.mem_univ,true_and]
    intro hb
    have noInternal (a : Point) (ha : a ∈ D) (h : e ∈ (Q r a).bonds) : False := by
      have hl := ((Box.mem_bonds _ _).mp h).1
      rcases he with (he|he)|he
      · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
      · rcases (mem_interface r v w e).mp he with he|he
        · exact hv ((cube_unique r he.1 hl) ▸ ha)
        · exact hw ((cube_unique r he.1 hl) ▸ ha)
    have noLink (a b : Point) (ha : a ∈ D) (h : e ∈ interface r a b) : False := by
      rcases (mem_interface r a b e).mp h with h|h
      · have hl := h.1
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).1 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hv ((cube_unique r he.1 hl) ▸ ha)
          · exact hw ((cube_unique r he.1 hl) ▸ ha)
      · have hl := h.2
        rcases he with (he|he)|he
        · exact hv ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · exact hw ((cube_unique r ((Box.mem_bonds _ _).mp he).2 hl) ▸ ha)
        · rcases (mem_interface r v w e).mp he with he|he
          · exact hw ((cube_unique r he.2 hl) ▸ ha)
          · exact hv ((cube_unique r he.2 hl) ▸ ha)
    rcases hb with ((hb|⟨d,hd⟩)|⟨a,ha,hb⟩)|⟨⟨a,b⟩,⟨ha,_⟩,hb⟩
    · exact noInternal 0 h0 hb
    · exact noLink 0 (outward d) h0 hd
    · exact noInternal a ha hb
    · exact noLink a b ha hb
  · change (Q r v).Contains e ∨ (Q r w).Contains e at he
    simp only [exposed,rootBits,linkBits,Box.bits,Finset.mem_union,Finset.mem_biUnion,
      Box.mem_vertices,Finset.notMem_empty,and_false,exists_false,or_false]
    rintro (hh|⟨a,ha,hh⟩)
    · rcases he with he|he
      · exact hv0 (cube_unique r he hh)
      · exact hw0 (cube_unique r he hh)
    · rcases he with he|he
      · exact hv ((cube_unique r he hh) ▸ ha)
      · exact hw ((cube_unique r he hh) ▸ ha)

noncomputable def extendGraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : LatticeGraph where
  vertices := G.vertices ∪ (Q r x).vertices
  edges := G.edges ∪ (Q r x).bonds ∪ interface r v x
  left_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.left_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).1)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.1))
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.1)
  right_mem := by
    intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (G.right_mem _ he)
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr ((Box.mem_bonds _ _).mp he).2)
    · rcases (mem_interface _ _ _ _).mp he with he|he
      · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr he.2)
      · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr he.2))

theorem extendGraph_subgraph (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : G.Subgraph (extendGraph r G v x hv) :=
  ⟨Finset.subset_union_left,fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)⟩

theorem extendGraph_contains (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsBox (Q r x) :=
  ⟨Finset.subset_union_right,fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)⟩

theorem extendGraph_bits (m : Model) (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) :
    (extendGraph r G v x hv).bits m = G.bits m ∪ block m r x v := by
  cases m
  · dsimp [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits]
    rw [interface_comm r x v,Finset.union_assoc]
  · simp only [LatticeGraph.bits,extendGraph,block,Box.bits,linkBits,Finset.union_empty]

theorem extendGraph_pair (r : ℕ) (G : LatticeGraph) (v x : Point)
    (hv : G.ContainsBox (Q r v)) : (extendGraph r G v x hv).ContainsSet (PairRegion r v x) := by
  constructor
  · intro y hy
    rcases hy with hy|hy
    · exact Finset.mem_union_left _ (hv.1 ((Box.mem_vertices _ _).mpr hy))
    · exact Finset.mem_union_right _ ((Box.mem_vertices _ _).mpr hy)
  · intro e he hf
    have hh := (internal_pair_bond r v x e).mp ⟨he,hf⟩
    rcases Finset.mem_union.mp hh with hh|hh
    · rcases Finset.mem_union.mp hh with hh|hh
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hv.2 hh))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hh)
    · exact Finset.mem_union_right _ hh
end Coarse
end CriticalZ3

end OAI
end
end

section
section
namespace OAI


open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

structure Scheme (E V S : Type) where
  reveal : S → Finset E
  parameter : S → E → Set.Icc (0 : ℝ) 1
  vertex : S → Option V
  bad : (s : S) → (reveal s → Bool) → Bool
  child : (s : S) → (reveal s → Bool) → S
  parameter_child : ∀ s a, parameter (child s a) =
    fixedParameter (parameter s) (reveal s) (ProductCylinder.extend (reveal s) a)

namespace Scheme
variable (P : Scheme E V S)

noncomputable def weight (s : S) (a : P.reveal s → Bool) : ℝ :=
  (ProductCylinder.law (P.parameter s)).real
    (pattern (P.reveal s) (ProductCylinder.extend (P.reveal s) a))

noncomputable def badMass (s : S) : ℝ :=
  ∑ a : P.reveal s → Bool, if P.bad s a = true then P.weight s a else 0

omit [Countable E] [DecidableEq V] in
theorem weight_nonneg (s : S) (a : P.reveal s → Bool) : 0 ≤ P.weight s a := measureReal_nonneg

omit [DecidableEq V] in
theorem weight_sum (s : S) : ∑ a : P.reveal s → Bool, P.weight s a = 1 :=
  sum_pattern_real _ _

/-- Every target must first be tested by the time limit, and its first test
must have declared it bad.  Removing it prevents multiple visits from ever
being counted as distinct successes in this estimate. -/
noncomputable def hit : ℕ → S → Finset V → Set (E → Bool)
  | 0, _, U => if U = ∅ then Set.univ else ∅
  | n+1, s, U => match P.vertex s with
    | none => if U = ∅ then Set.univ else ∅
    | some v => {ω | (v ∈ U → P.bad s ((P.reveal s).restrict ω) = true) ∧
        ω ∈ hit n (P.child s ((P.reveal s).restrict ω)) (U.erase v)}

theorem measurableSet_hit (n : ℕ) (s : S) (U : Finset V) : MeasurableSet (P.hit n s U) := by
  induction n generalizing s U with
  | zero => simp only [hit]; split_ifs <;> simp
  | succ n ih =>
    simp only [hit]
    split
    · split_ifs <;> simp
    · rename_i v hv
      apply measurableSet_select (P.reveal s)
        (fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)})
      intro a
      by_cases h : v ∈ U → P.bad s a = true
      · convert ih (P.child s a) (U.erase v) using 1
        ext ω; exact and_iff_right h
      · simp only [h,false_and,Set.ofPred_false]; exact MeasurableSet.empty

omit [Countable E] in
theorem hit_empty (n : ℕ) (s : S) : P.hit n s ∅ = Set.univ := by
  induction n generalizing s with
  | zero => simp [hit]
  | succ n ih =>
    simp only [hit]
    cases P.vertex s <;> simp [ih]

/-- The only probabilistic hypotheses are the local bad probability and the
exact next-history product law.  Invalid zero-mass histories need no promise. -/
theorem hit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (n : ℕ) (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (P.hit n s U) ≤ f^U.card := by
  induction n generalizing s U with
  | zero =>
    by_cases hu : U = ∅
    · simp [hit,hu,probReal_univ]
    · simp only [hit,ite_eq_right hu,measureReal_empty]
      exact pow_nonneg hf _
  | succ n ih =>
    cases hv : P.vertex s with
    | none =>
      by_cases hu : U = ∅
      · simp [hit,hv,hu,probReal_univ]
      · simp only [hit,hv,ite_eq_right hu,measureReal_empty]
        exact pow_nonneg hf _
    | some v =>
      let A : (P.reveal s → Bool) → Set (E → Bool) :=
        fun a => {ω | (v ∈ U → P.bad s a = true) ∧ ω ∈ P.hit n (P.child s a) (U.erase v)}
      have hA (a) : MeasurableSet (A a) := by
        by_cases ha : v ∈ U → P.bad s a = true
        · convert P.measurableSet_hit n (P.child s a) (U.erase v) using 1
          ext ω; exact and_iff_right ha
        · simp only [A,ha,false_and,Set.ofPred_false]; exact MeasurableSet.empty
      simp only [hit,hv]
      change (ProductCylinder.law (P.parameter s)).real
        {ω | ω ∈ A ((P.reveal s).restrict ω)} ≤ _
      rw [measure_select _ _ A hA]
      change (∑ a, P.weight s a *
        (ProductCylinder.law (fixedParameter (P.parameter s) (P.reveal s)
          (ProductCylinder.extend (P.reveal s) a))).real (A a)) ≤ _
      simp_rw [←P.parameter_child]
      have hterm (a) : P.weight s a *
          (ProductCylinder.law (P.parameter (P.child s a))).real (A a) ≤
          (if v ∈ U → P.bad s a = true then P.weight s a else 0) * f^(U.erase v).card := by
        by_cases hw : P.weight s a = 0
        · simp [hw]
        have hpos : 0 < P.weight s a := lt_of_le_of_ne (P.weight_nonneg s a) (Ne.symm hw)
        by_cases ha : v ∈ U → P.bad s a = true
        · have heqA : A a = P.hit n (P.child s a) (U.erase v) := by
            ext ω; exact and_iff_right ha
          rw [heqA,ite_eq_left ha]
          exact mul_le_mul_of_nonneg_left (ih (P.child s a) (hchild s hs a hpos) (U.erase v))
            (P.weight_nonneg s a)
        · simp only [A,ha,false_and,Set.ofPred_false,measureReal_empty,ite_false,mul_zero,zero_mul]
          exact le_rfl
      apply (Finset.sum_le_sum (fun a _ => hterm a)).trans
      rw [←Finset.sum_mul]
      by_cases hmem : v ∈ U
      · simp only [hmem,true_implies]
        change P.badMass s * f^(U.erase v).card ≤ f^U.card
        have hcard : (U.erase v).card + 1 = U.card := Finset.card_erase_add_one hmem
        rw [←hcard,pow_succ']
        exact mul_le_mul_of_nonneg_right (hbad s hs) (pow_nonneg hf _)
      · simp only [hmem,false_implies,ite_true,P.weight_sum,one_mul,Finset.erase_eq_of_notMem hmem]
        exact le_rfl

omit [DecidableEq V] in
theorem badMass_eq_probability (s : S) : P.badMass s =
    (ProductCylinder.law (P.parameter s)).real
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by
  have h := measure_select (P.parameter s) (P.reveal s)
    (fun a => if P.bad s a = true then Set.univ else ∅)
    (fun a => by split_ifs <;> simp)
  have heq : {ω : E → Bool | ω ∈ if P.bad s ((P.reveal s).restrict ω) = true then Set.univ else ∅} =
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by aesop
  rw [heq] at h
  rw [h]
  unfold badMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.bad s a = true <;> simp [weight,ha,probReal_univ]

omit [Countable E] in
theorem hit_subset_succ (n : ℕ) (s : S) (U : Finset V) :
    P.hit n s U ⊆ P.hit (n+1) s U := by
  induction n generalizing s U with
  | zero =>
    by_cases hU : U = ∅
    · subst U; rw [P.hit_empty,P.hit_empty]
    · simp only [hit,ite_eq_right hU]; exact Set.empty_subset _
  | succ n ih =>
    cases hv : P.vertex s with
    | none => simp only [hit,hv]; exact Set.Subset.rfl
    | some v =>
      simp only [hit,hv]
      intro ω hω
      exact ⟨hω.1,ih _ _ hω.2⟩

omit [Countable E] in
theorem hit_monotone (s : S) (U : Finset V) : Monotone (fun n => P.hit n s U) :=
  monotone_nat_of_le_succ (fun n => P.hit_subset_succ n s U)

/-- Uniform control survives an unbounded possible processing time. -/
theorem everHit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (⋃ n, P.hit n s U) ≤ f^U.card := by
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top (ProductCylinder.law (P.parameter s))
    (⋃ n, P.hit n s U))).comp
    (tendsto_measure_iUnion_atTop (μ := ProductCylinder.law (P.parameter s)) (P.hit_monotone s U))
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n => P.hit_bound I f hf hbad hchild n s hs U)

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem fixedParameter_merge (p : E → Set.Icc (0:ℝ) 1) (J K : Finset E)
    (ξ ω : E → Bool) : fixedParameter (fixedParameter p J ξ) K ω =
      fixedParameter p (J ∪ K) (replace K ω ξ) := by
  funext e
  by_cases hK : e ∈ K <;> by_cases hJ : e ∈ J <;>
    simp [fixedParameter,replace,hK,hJ]

structure History (E : Type) where
  known : Finset E
  values : E → Bool

namespace History
noncomputable def parameter (h : History E) (q : Set.Icc (0:ℝ) 1) :=
  fixedParameter (fun _ => q) h.known h.values
noncomputable def observe (h : History E) (R : Finset E) (ω : E → Bool) : History E :=
  ⟨h.known ∪ R,replace R ω h.values⟩
noncomputable def freeze (h : History E) (ω : E → Bool) := replace h.known h.values ω

omit [Countable E] in
theorem parameter_observe (h : History E) (q : Set.Icc (0:ℝ) 1) (R : Finset E) (ω : E → Bool) :
    (h.observe R ω).parameter q = fixedParameter (h.parameter q) R ω :=
  (fixedParameter_merge _ _ _ _ _).symm

omit [Countable E] in
theorem freeze_determined (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) :
    ∀ ω ω', (∀ e ∈ R, ω' e = ω e) → f (h.freeze ω') = f (h.freeze ω) := by
  intro ω ω' he
  apply hf
  intro e heJ
  by_cases hk : e ∈ h.known
  · simp only [freeze,replace,ite_eq_left hk]
  · have hr := (Finset.mem_union.mp (hJ heJ)).resolve_left hk
    simp only [freeze,replace,ite_eq_right hk,he e hr]

omit [Countable E] in
theorem observe_outcome (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) (hR : Disjoint R h.known) (ω : E → Bool) :
    f (h.observe R ω).values = f (h.freeze ω) := by
  apply hf
  intro e he
  rcases Finset.mem_union.mp (hJ he) with hk|hr
  · have hn : e ∉ R := fun hh => Finset.disjoint_left.mp hR hh hk
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hk]
  · have hn : e ∉ h.known := fun hh => Finset.disjoint_left.mp hR hr hh
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hr]

theorem ae_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) :
    ∀ᵐ ω ∂ProductCylinder.law (h.parameter q), h.freeze ω = ω := by
  filter_upwards [ae_fixed_pattern (fun _ => q) h.known h.values] with ω hω
  exact replace_eq_of_pattern hω

theorem probability_freeze (h : History E) (q : Set.Icc (0:ℝ) 1) (A : Set (E → Bool)) :
    (ProductCylinder.law (h.parameter q)).real {ω | h.freeze ω ∈ A} =
      (ProductCylinder.law (h.parameter q)).real A := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [h.ae_freeze q] with ω hω
  show (h.freeze ω ∈ A) = (ω ∈ A)
  rw [hω]
end History
end InfiniteConditioning

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

/-- A packet stores exactly the finite parent-chain graph, extended only on assignment. -/
structure Packet (r : ℕ) where
  vertex : Point
  parent : Point
  graph : LatticeGraph
  contains : graph.ContainsBox (Q r vertex)
  root_mem : (0:Vertex) ∈ graph.vertices

namespace Packet
variable {r : ℕ}
def event (t : Packet r) (m : Model) : Set m.Config :=
  {ω | t.graph.Meets m ω ⟨0,t.root_mem⟩ {y | (B r t.vertex).Contains y}}

theorem measurableSet_event (t : Packet r) (m : Model) : MeasurableSet (t.event m) :=
  t.graph.measurableSet_meets m _ _

theorem event_determined (t : Packet r) (m : Model) :
    ProductCylinder.DeterminedBy (F := Prop) (t.graph.bits m) (fun ω => ω ∈ t.event m) :=
  t.graph.meets_determined m _ _

noncomputable def child (t : Packet r) (x : Point) : Packet r where
  vertex := x
  parent := t.vertex
  graph := extendGraph r t.graph t.vertex x t.contains
  contains := extendGraph_contains r t.graph t.vertex x t.contains
  root_mem := (extendGraph_subgraph r t.graph t.vertex x t.contains).1 t.root_mem

theorem child_bits (t : Packet r) (x : Point) (m : Model) :
    (t.child x).graph.bits m = t.graph.bits m ∪ block m r x t.vertex :=
  extendGraph_bits m r t.graph t.vertex x t.contains
end Packet

structure Exploration (m : Model) (r : ℕ) where
  history : History m.Bit
  processed : Finset Point
  queue : List (Packet r)
  good : Finset Point
  bad : Finset Point

namespace Exploration
variable {m : Model} {r : ℕ}
noncomputable def visited (s : Exploration m r) : Finset Point :=
  s.processed ∪ (s.queue.map Packet.vertex).toFinset
noncomputable def reveal (s : Exploration m r) : Finset m.Bit :=
  match s.queue with
  | [] => ∅
  | t::_ => block m r t.vertex t.parent \ s.history.known
noncomputable def after (s : Exploration m r) (ω : m.Config) : History m.Bit :=
  s.history.observe s.reveal ω
noncomputable def candidates (s : Exploration m r) (t : Packet r) : List (Packet r) :=
  (List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).filter
    (fun u => u.vertex ∉ s.visited)
noncomputable def Accept (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (t : Packet r) (ω : m.Config) : Prop :=
  (s.after ω).values ∈ t.event m ∧ ∀ u ∈ s.candidates t,
    1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
noncomputable def markedBad (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Bool :=
  match s.queue with
  | [] => false
  | t::_ => decide (¬s.Accept q δ t ω)
noncomputable def advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) : Exploration m r where
  history := s.after ω
  processed := match s.queue with | [] => s.processed | t::_ => insert t.vertex s.processed
  queue := match s.queue with
    | [] => []
    | t::ts => ts ++ if s.Accept q δ t ω then s.candidates t else []
  good := match s.queue with
    | [] => s.good
    | t::_ => if s.Accept q δ t ω then insert t.vertex s.good else s.good
  bad := match s.queue with
    | [] => s.bad
    | t::_ => if s.Accept q δ t ω then s.bad else insert t.vertex s.bad

theorem reveal_disjoint (s : Exploration m r) : Disjoint s.reveal s.history.known := by
  cases h : s.queue with
  | nil => simp only [reveal,h]; exact Finset.disjoint_empty_left _
  | cons t ts => simp only [reveal,h]; exact Finset.sdiff_disjoint

noncomputable def scheme (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    AdaptiveReveals.Scheme m.Bit Point (Exploration m r) where
  reveal := reveal
  parameter := fun s => s.history.parameter q
  vertex := fun s => (s.queue.head?).map Packet.vertex
  bad := fun s a => s.markedBad q δ (ProductCylinder.extend s.reveal a)
  child := fun s a => s.advance q δ (ProductCylinder.extend s.reveal a)
  parameter_child := fun s _a => s.history.parameter_observe q s.reveal _

structure Valid (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) : Prop where
  root_processed : 0 ∈ s.processed
  distinct : (s.queue.map Packet.vertex).Nodup
  unprocessed : ∀ t ∈ s.queue, t.vertex ∉ s.processed
  parents : ∀ t ∈ s.queue, t.parent ∈ s.processed
  exposed : s.history.known ⊆ Coarse.exposed m r s.processed
  support : ∀ t ∈ s.queue, t.graph.bits m ⊆ s.history.known ∪ block m r t.vertex t.parent
  promise : ∀ t ∈ s.queue, 1-δ < (ProductCylinder.law (s.history.parameter q)).real (t.event m)
end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem outward_injective : Function.Injective outward := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [outward,PlanarBoundary.outward]

theorem neighbor_ne (v : Point) (d : Direction) : v+outward d ≠ v := by
  intro h
  have hh : outward d = 0 := add_left_cancel (h.trans (add_zero v).symm)
  fin_cases d <;> norm_num [outward,PlanarBoundary.outward] at hh

namespace Exploration
variable {m : Model} {r : ℕ}

@[simp] theorem mem_candidates (s : Exploration m r) (t u : Packet r) :
    u ∈ s.candidates t ↔ (∃ d : Direction, t.child (t.vertex+outward d) = u) ∧ u.vertex ∉ s.visited := by
  simp only [candidates,List.mem_filter,List.mem_ofFn,decide_eq_true_eq]

theorem queue_visited (s : Exploration m r) {t : Packet r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

theorem candidates_distinct (s : Exploration m r) (t : Packet r) :
    ((s.candidates t).map Packet.vertex).Nodup := by
  have hh : ((List.ofFn (fun d : Direction => t.child (t.vertex+outward d))).map Packet.vertex).Nodup := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro a b hab
    exact outward_injective (add_left_cancel hab)
  exact (List.filter_sublist.map Packet.vertex).nodup hh

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

theorem current_support {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    t.graph.bits m ⊆ s.history.known ∪ s.reveal := by
  intro e he
  have hh := hs.support t (by simp [hq]) he
  rcases Finset.mem_union.mp hh with hh|hh
  · exact Finset.mem_union_left _ hh
  · by_cases hk : e ∈ s.history.known
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (by simpa only [reveal,hq,Finset.mem_sdiff] using ⟨hh,hk⟩)

theorem later_disjoint {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) : Disjoint s.reveal (u.graph.bits m) := by
  have htq : t ∈ s.queue := by simp [hq]
  have huq : u ∈ s.queue := by simp [hq,hu]
  have htu : t.vertex ≠ u.vertex := by
    have hn := hs.distinct
    rw [hq,List.map_cons,List.nodup_cons] at hn
    intro he
    exact hn.1 (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩)
  have hd := block_disjoint m r (hs.unprocessed t htq) (hs.unprocessed u huq)
    (hs.parents t htq) (hs.parents u huq) htu
  apply Finset.disjoint_left.mpr
  intro e he hu
  have hr : e ∈ block m r t.vertex t.parent ∧ e ∉ s.history.known := by
    simpa only [reveal,hq,Finset.mem_sdiff] using he
  rcases Finset.mem_union.mp (hs.support u huq hu) with hu|hu
  · exact hr.2 hu
  · exact Finset.disjoint_left.mp hd hr.1 hu

theorem later_probability {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {u : Packet r} (hu : u ∈ ts) (ω : m.Config) :
    (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m) =
      (ProductCylinder.law (s.history.parameter q)).real (u.event m) := by
  apply ProductCylinder.probability_congr_parameters (u.graph.bits m) _ _ _ _ (u.event_determined m)
  intro e he
  rw [after,History.parameter_observe]
  exact ite_eq_right (fun hh => Finset.disjoint_left.mp (later_disjoint hs hq hu) hh he)

theorem valid_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (ω : m.Config) : (s.advance q δ ω).Valid q δ := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    have htq : t ∈ s.queue := by simp [hq]
    have hnot : t.vertex ∉ ts.map Packet.vertex := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.1
    have htail : (ts.map Packet.vertex).Nodup := by
      have hh := hs.distinct
      rw [hq,List.map_cons,List.nodup_cons] at hh
      exact hh.2
    have hp : (s.advance q δ ω).processed = insert t.vertex s.processed := by simp [advance,hq]
    have hn : (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
      simp [advance,hq]
    have hvu {u : Packet r} (hu : u ∈ s.candidates t) :
        u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      have hh := (mem_candidates s t u).mp hu |>.2
      exact ⟨fun he => hh (he ▸ s.queue_visited htq),fun he => hh (s.processed_visited he)⟩
    have hold {u : Packet r} (hu : u ∈ ts) : u.vertex ≠ t.vertex ∧ u.vertex ∉ s.processed := by
      exact ⟨fun he => hnot (he ▸ List.mem_map.mpr ⟨u,hu,rfl⟩),
        hs.unprocessed u (by simp [hq,hu])⟩
    have hmembers {u : Packet r} (hu : u ∈ (s.advance q δ ω).queue) :
        u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
      rw [hn,List.mem_append] at hu
      rcases hu with hu|hu
      · exact Or.inl hu
      · split_ifs at hu with ha
        · exact Or.inr ⟨ha,hu⟩
        · exact False.elim (List.not_mem_nil hu)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [hp]; exact Finset.mem_insert_of_mem hs.root_processed
    · rw [hn,List.map_append]
      split_ifs with ha
      · apply htail.append (s.candidates_distinct t)
        apply List.disjoint_left.mpr
        intro v hv hu
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hu
        have hh := (mem_candidates s t z).mp hz |>.2
        exact hh (Finset.mem_union_right _ (List.mem_toFinset.mpr (by rw [hq,List.map_cons]; exact List.mem_cons_of_mem _ hv)))
      · simpa only [List.map_nil,List.append_nil] using htail
    · intro u hu
      rw [hp,Finset.mem_insert]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact not_or.mpr (hold hu)
      · exact not_or.mpr (hvu hu)
    · intro u hu
      rw [hp]
      rcases hmembers hu with hu|⟨_,hu⟩
      · exact Finset.mem_insert_of_mem (hs.parents u (by simp [hq,hu]))
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        exact Finset.mem_insert_self _ _
    · rw [hp]
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      intro e he
      rcases he with hk|hr
      · exact exposed_mono m r (Finset.subset_insert _ _) (hs.exposed hk)
      · apply block_subset_exposed_insert m r (hs.parents t htq)
        exact (Finset.mem_sdiff.mp (by simpa only [reveal,hq] using hr)).1
    · intro u hu
      dsimp only [advance,after,History.observe]
      simp only [Finset.subset_iff,Finset.mem_union]
      rcases hmembers hu with hu|⟨_,hu⟩
      · intro e he
        rcases Finset.mem_union.mp (hs.support u (by simp [hq,hu]) he) with he|he
        · exact Or.inl (Or.inl he)
        · exact Or.inr he
      · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
        intro e he
        rw [Packet.child_bits,Finset.mem_union] at he
        rcases he with he|he
        · exact Or.inl (Finset.mem_union.mp (current_support hs hq he))
        · exact Or.inr he
    · intro u hu
      rcases hmembers hu with hu|⟨ha,hu⟩
      · change 1-δ < (ProductCylinder.law ((s.after ω).parameter q)).real (u.event m)
        rw [later_probability hs hq hu ω]
        exact hs.promise u (by simp [hq,hu])
      · exact ha.2 u hu
end Exploration
end Coarse
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem after_determined (s : Exploration m r) :
    ProductCylinder.DeterminedBy s.reveal (s.after) := by
  intro ω ω' he
  unfold after History.observe
  congr 1
  funext e
  by_cases hr : e ∈ s.reveal
  · simp only [replace,ite_eq_left hr,he e hr]
  · simp only [replace,ite_eq_right hr]

theorem markedBad_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.markedBad q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [markedBad,hq,ha]

theorem advance_determined (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    ProductCylinder.DeterminedBy s.reveal (s.advance q δ) := by
  intro ω ω' he
  have h := s.after_determined ω ω' he
  have ha (t : Packet r) : s.Accept q δ t ω' ↔ s.Accept q δ t ω := by simp only [Accept,h]
  cases hq : s.queue <;> simp only [advance,hq,h,ha]

theorem badMass_eq (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) :
    (scheme (r := r) q δ).badMass s =
      (ProductCylinder.law (s.history.parameter q)).real {ω | s.markedBad q δ ω = true} := by
  rw [AdaptiveReveals.Scheme.badMass_eq_probability]
  congr 2
  ext ω
  change (s.markedBad q δ (ProductCylinder.extend s.reveal (s.reveal.restrict ω)) = true) ↔ _
  rw [←ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω]

noncomputable def frozenEvent (s : Exploration m r) (t : Packet r) : Set m.Config :=
  {ω | s.history.freeze ω ∈ t.event m}

theorem frozenEvent_determined {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    ProductCylinder.DeterminedBy (F := Prop) s.reveal (fun ω => ω ∈ s.frozenEvent t) :=
  s.history.freeze_determined _ (t.event_determined m) (by
    simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq)

theorem frozenEvent_probability (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (t : Packet r) :
    (ProductCylinder.law (s.history.parameter q)).real (s.frozenEvent t) =
      (ProductCylinder.law (s.history.parameter q)).real (t.event m) :=
  s.history.probability_freeze q (t.event m)

theorem accept_current_iff {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) (ω : m.Config) :
    (s.after ω).values ∈ t.event m ↔ ω ∈ s.frozenEvent t := by
  exact Eq.to_iff (s.history.observe_outcome _ (t.event_determined m)
    (by simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq) s.reveal_disjoint ω)

theorem relay_failure (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) {t : Packet sc.r} {ts : List (Packet sc.r)} (hq : s.queue = t::ts)
    (d : Direction) (hx : t.vertex+outward d ∉ s.visited) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) ≤ 13*sc.η := by
  have htq : t ∈ s.queue := by simp [hq]
  have hv := hs.unprocessed t htq
  have hxD : t.vertex+outward d ∉ s.processed := fun hh => hx (s.processed_visited hh)
  have hv0 : t.vertex ≠ 0 := fun he => hv (he ▸ hs.root_processed)
  have hx0 : t.vertex+outward d ≠ 0 := fun he => hxD (he ▸ hs.root_processed)
  have hfresh : m.UniformOn (s.history.parameter sc.q) sc.q
      (PairRegion sc.r t.vertex (t.vertex+outward d)) := by
    intro e he
    apply ite_eq_right
    intro hk
    exact internal_pair_not_exposed m sc.r hs.root_processed hv hxD he (hs.exposed hk)
  have hrelay := neighboring_relay sc (t.child (t.vertex+outward d)).graph
    (s.history.parameter sc.q) t.vertex d
    (extendGraph_pair sc.r t.graph t.vertex _ t.contains) hfresh
    ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ (zero_outside_pair sc.r hv0 hx0)
  have hi : t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ ⊆
      {ω | (t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r t.vertex).Contains y} ∧
          ¬(t.child (t.vertex+outward d)).graph.Meets m ω
        ⟨0,(t.child (t.vertex+outward d)).root_mem⟩ {y | (B sc.r (t.vertex+outward d)).Contains y}} := by
    intro ω hω
    exact ⟨LatticeGraph.meets_inclusion (extendGraph_subgraph sc.r t.graph t.vertex _ t.contains) m hω.1,hω.2⟩
  have heq : (ProductCylinder.law (s.history.parameter sc.q)).real
      (s.frozenEvent t ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) =
      (ProductCylinder.law (s.history.parameter sc.q)).real
      (t.event m ∩ ((t.child (t.vertex+outward d)).event m)ᶜ) := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [s.history.ae_freeze sc.q] with ω hω
    change ((s.history.freeze ω ∈ t.event m) ∧ _) = ((ω ∈ t.event m) ∧ _)
    rw [hω]
  rw [heq]
  exact (measureReal_mono hi).trans hrelay

theorem badMass_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) :
    (scheme (r := sc.r) sc.q sc.δ).badMass s ≤ CriticalScales.contourError := by
  rw [badMass_eq]
  cases hq : s.queue with
  | nil => simpa only [markedBad,hq,Bool.false_eq_true,Set.ofPred_false,measureReal_empty] using
      CriticalScales.contourError_pos.le
  | cons t ts =>
    let μ := ProductCylinder.law (s.history.parameter sc.q)
    let H := s.frozenEvent t
    let T (d : Direction) : Set m.Config :=
      {ω | ω ∈ H ∧ t.vertex+outward d ∉ s.visited ∧
        (ProductCylinder.law ((s.after ω).parameter sc.q)).real
          ((t.child (t.vertex+outward d)).event m) ≤ 1-sc.δ}
    have hH := frozenEvent_determined hs hq
    have hHm : MeasurableSet H := ProductCylinder.measurableSet_determined _ _
      (fun ω ω' he => Eq.to_iff (hH ω ω' he))
    have hHprob : μ.real Hᶜ < sc.δ := by
      rw [measureReal_compl hHm,probReal_univ]
      have hh := hs.promise t (by simp [hq])
      have he := s.frozenEvent_probability sc.q t
      change μ.real H = μ.real (t.event m) at he
      rw [he]
      linarith
    have hT (d : Direction) : μ.real (T d) ≤ (13*sc.η)/sc.δ := by
      by_cases hx : t.vertex+outward d ∉ s.visited
      · have hh := conditional_failure_bound (s.history.parameter sc.q) s.reveal H
          ((t.child (t.vertex+outward d)).event m) hH
          ((t.child (t.vertex+outward d)).measurableSet_event m) sc.δ_range.1
          (relay_failure sc hs hq d hx)
        have he : T d = {ω | ω ∈ H ∧ conditionalProbability (s.history.parameter sc.q)
            s.reveal ((t.child (t.vertex+outward d)).event m) ω ≤ 1-sc.δ} := by
          ext ω
          simp only [T,hx,not_false_eq_true,true_and,Set.mem_ofPred_eq,after,History.parameter_observe,
            conditionalProbability]
        rwa [he]
      · have he : T d = ∅ := by ext ω; simp only [T,hx,false_and,and_false,Set.mem_ofPred_eq,Set.mem_empty_iff_false]
        rw [he,measureReal_empty]
        exact div_nonneg (mul_nonneg (by norm_num) sc.η_range.1.le) sc.δ_range.1.le
    have hb : {ω | s.markedBad sc.q sc.δ ω = true} ⊆ Hᶜ ∪ ⋃ d, T d := by
      intro ω hω
      have hn : ¬s.Accept sc.q sc.δ t ω := by
        simpa only [Set.mem_ofPred_eq,markedBad,hq,decide_eq_true_eq] using hω
      by_cases hh : ω ∈ H
      · right
        have hcur := (accept_current_iff hs hq ω).mpr hh
        have hpred : ¬∀ u ∈ s.candidates t, 1-sc.δ <
            (ProductCylinder.law ((s.after ω).parameter sc.q)).real (u.event m) :=
          fun hp => hn ⟨hcur,hp⟩
        push Not at hpred
        obtain ⟨u,hu,hfail⟩ := hpred
        obtain ⟨⟨d,rfl⟩,hx⟩ := (mem_candidates s t u).mp hu
        exact Set.mem_iUnion.mpr ⟨d,hh,hx,hfail⟩
      · exact Or.inl hh
    calc
      _ ≤ μ.real (Hᶜ ∪ ⋃ d, T d) := measureReal_mono hb
      _ ≤ μ.real Hᶜ + μ.real (⋃ d, T d) := measureReal_union_le _ _
      _ ≤ μ.real Hᶜ + ∑ d, μ.real (T d) := add_le_add le_rfl (measureReal_iUnion_fintype_le _)
      _ ≤ μ.real Hᶜ + ∑ _d : Direction, (13*sc.η)/sc.δ :=
        add_le_add le_rfl (Finset.sum_le_sum (fun d _ => hT d))
      _ = μ.real Hᶜ + 52*sc.η/sc.δ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ sc.δ + 52*sc.η/sc.δ := add_le_add hHprob.le le_rfl
      _ ≤ CriticalScales.contourError := sc.failure_budget.le

theorem everHit_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (⋃ n, (scheme (r := sc.r) sc.q sc.δ).hit n s U) ≤ CriticalScales.contourError^U.card := by
  apply AdaptiveReveals.Scheme.everHit_bound _ (Valid sc.q sc.δ) _ CriticalScales.contourError_pos.le
    (fun _ hs => badMass_bound sc hs) _ s hs U
  intro s hs a _
  exact valid_advance hs _
end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem advance_processed (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).processed = insert t.vertex s.processed := by simp only [advance,hq]

theorem advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
  simp only [advance,hq]

theorem mem_advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t u : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    u ∈ (s.advance q δ ω).queue ↔ u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
  rw [s.advance_queue q δ ω hq,List.mem_append]
  by_cases h : s.Accept q δ t ω <;> simp [h]

theorem processed_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.processed ⊆ (s.advance q δ ω).processed := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · rw [s.advance_processed q δ ω hq]; exact Finset.subset_insert _ _

theorem good_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.good ⊆ (s.advance q δ ω).good := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem bad_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.bad ⊆ (s.advance q δ ω).bad := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

theorem visited_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.visited ⊆ (s.advance q δ ω).visited := by
  cases hq : s.queue with
  | nil => rw [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact (s.advance q δ ω).processed_visited (s.processed_advance_mono q δ ω hv)
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
      rw [hq,List.mem_cons] at hu
      rcases hu with rfl|hu
      · apply (s.advance q δ ω).processed_visited
        rw [s.advance_processed q δ ω hq]
        exact Finset.mem_insert_self _ _
      · apply (s.advance q δ ω).queue_visited
        exact (s.mem_advance_queue q δ ω hq).mpr (Or.inl hu)

theorem new_visited (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {v : Point} (hv : v ∈ (s.advance q δ ω).visited) :
    v ∈ s.visited ∨ (s.Accept q δ t ω ∧ ∃ d : Direction, v = t.vertex+outward d) := by
  rcases Finset.mem_union.mp hv with hv|hv
  · rw [s.advance_processed q δ ω hq,Finset.mem_insert] at hv
    rcases hv with rfl|hv
    · exact Or.inl (s.queue_visited (by simp [hq]))
    · exact Or.inl (s.processed_visited hv)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    rcases (s.mem_advance_queue q δ ω hq).mp hu with hu|⟨ha,hu⟩
    · exact Or.inl (s.queue_visited (by simp [hq,hu]))
    · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
      exact Or.inr ⟨ha,d,rfl⟩

theorem accepted_neighbors (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    (ha : s.Accept q δ t ω) (d : Direction) :
    t.vertex+outward d ∈ (s.advance q δ ω).visited := by
  by_cases hv : t.vertex+outward d ∈ s.visited
  · exact s.visited_advance_mono q δ ω hv
  · apply (s.advance q δ ω).queue_visited (t := t.child (t.vertex+outward d))
    apply (s.mem_advance_queue q δ ω hq).mpr
    exact Or.inr ⟨ha,(mem_candidates _ _ _).mpr ⟨⟨d,rfl⟩,hv⟩⟩

structure Colored (s : Exploration m r) : Prop where
  partition : s.processed = s.good ∪ s.bad
  disjoint : Disjoint s.good s.bad

def Closed (s : Exploration m r) : Prop :=
  ∀ v ∈ s.good, ∀ d : Direction, v+outward d ∈ s.visited

def Covered (s : Exploration m r) : Prop :=
  ∀ v ∈ s.visited, v ∈ s.good ∨ ∃ u ∈ s.good, ∃ d : Direction, v = u+outward d

theorem Colored.good_processed {s : Exploration m r} (h : s.Colored) : s.good ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_left

theorem Colored.bad_processed {s : Exploration m r} (h : s.Colored) : s.bad ⊆ s.processed := by
  rw [h.partition]; exact Finset.subset_union_right

theorem colored_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (ω : m.Config) : (s.advance q δ ω).Colored := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    have hn := hs.unprocessed t (by simp [hq])
    have hng : t.vertex ∉ s.good := fun h => hn (hc.good_processed h)
    have hnb : t.vertex ∉ s.bad := fun h => hn (hc.bad_processed h)
    constructor
    · simp only [advance,hq]
      split_ifs <;> simp only [hc.partition,Finset.insert_union,Finset.union_insert]
    · simp only [advance,hq]
      split_ifs
      · exact Finset.disjoint_insert_left.mpr ⟨hnb,hc.disjoint⟩
      · exact Finset.disjoint_insert_right.mpr ⟨hng,hc.disjoint⟩

theorem closed_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Closed) (ω : m.Config) : (s.advance q δ ω).Closed := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv d
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact s.accepted_neighbors q δ ω hq ha d
      · exact s.visited_advance_mono q δ ω (hc _ hv d)
    · exact s.visited_advance_mono q δ ω (hc _ hv d)

theorem covered_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Covered) (ω : m.Config) : (s.advance q δ ω).Covered := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases s.new_visited q δ ω hq hv with hv|⟨ha,d,rfl⟩
    · rcases hc _ hv with hv|⟨u,hu,d,he⟩
      · exact Or.inl (s.good_advance_mono q δ ω hv)
      · exact Or.inr ⟨u,s.good_advance_mono q δ ω hu,d,he⟩
    · right
      refine ⟨t.vertex,?_,d,rfl⟩
      simp only [advance,hq,ite_eq_left ha]
      exact Finset.mem_insert_self _ _

noncomputable def run (q : Set.Icc (0:ℝ) 1) (δ : ℝ) : ℕ → Exploration m r → m.Config → Exploration m r
  | 0,s,_ => s
  | n+1,s,ω => run q δ n (s.advance q δ ω) ω

@[simp] theorem run_zero (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    run q δ 0 s ω = s := rfl

@[simp] theorem run_succ (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = run q δ n (s.advance q δ ω) ω := rfl

theorem run_succ_right (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = (run q δ n s ω).advance q δ ω := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run_succ,ih,run_succ]

theorem run_valid {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Valid q δ := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (valid_advance hs ω)

theorem run_colored {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Colored := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (valid_advance hs ω) (colored_advance hs hc ω)

theorem run_closed (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Closed) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Closed := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (closed_advance s q δ hc ω)

theorem run_covered (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Covered) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Covered := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (covered_advance s q δ hc ω)

theorem run_good_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).good) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact good_advance_mono _ _ _ _

theorem run_bad_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).bad) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact bad_advance_mono _ _ _ _

theorem run_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r} (hs : s.queue = [])
    (n : ℕ) (ω : m.Config) : run q δ n s ω = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,advance_empty s q δ ω hs,ih]

noncomputable def Good (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) : Set Point :=
  {v | ∃ n, v ∈ (run q δ n s ω).good}
noncomputable def Bad (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (v : Point) : Set m.Config :=
  {ω | ∃ n, v ∈ (run q δ n s ω).bad}

theorem initial_good_subset (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    (s.good : Set Point) ⊆ Good q δ s ω := fun _ hv => ⟨0,hv⟩

end Coarse.Exploration
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem run_add (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (a b : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (a+b) s ω = run q δ b (run q δ a s ω) ω := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,run_zero]
  | succ a ih => rw [Nat.succ_add,run_succ,ih,run_succ]

theorem run_stable (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N k : ℕ} (hN : (run q δ N s ω).queue = []) (hk : N ≤ k) :
    run q δ k s ω = run q δ N s ω := by
  rw [←Nat.add_sub_of_le hk,run_add]
  exact run_empty q δ hN _ ω

theorem good_eq_of_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N : ℕ} (hN : (run q δ N s ω).queue = []) :
    Good q δ s ω = ((run q δ N s ω).good : Set Point) := by
  ext v
  constructor
  · rintro ⟨k,hk⟩
    have hh := run_good_mono q δ s ω (show k ≤ N+k by omega) hk
    dsimp only at hh
    rwa [run_stable q δ s ω hN (show N ≤ N+k by omega)] at hh
  · intro h; exact ⟨N,h⟩

theorem exists_empty_of_finite_good {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Covered) (ω : m.Config) (hfin : (Good q δ s ω).Finite) :
    ∃ n, (run q δ n s ω).queue = [] := by
  let X := Good q δ s ω
  let F := X ∪ ⋃ d : Direction, (fun v : Point => v+outward d) '' X
  have hF : F.Finite := hfin.union (Set.finite_iUnion (fun d => hfin.image _))
  have hbound (n : ℕ) : (run q δ n s ω).processed ⊆ hF.toFinset := by
    intro v hv
    apply hF.mem_toFinset.mpr
    have hh := run_covered q δ hc n ω v ((run q δ n s ω).processed_visited hv)
    rcases hh with hv|⟨u,hu,d,rfl⟩
    · exact Or.inl ⟨n,hv⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨d,u,⟨n,hu⟩,rfl⟩)
  by_contra! hn
  have hcard (n : ℕ) : s.processed.card+n ≤ (run q δ n s ω).processed.card := by
    induction n with
    | zero => simp only [run_zero,Nat.add_zero,le_refl]
    | succ n ih =>
      have hvalid := run_valid hs n ω
      cases hq : (run q δ n s ω).queue with
      | nil => exact False.elim (hn n hq)
      | cons t ts =>
        rw [run_succ_right,advance_processed _ q δ ω hq,
          Finset.card_insert_of_notMem (hvalid.unprocessed t (by simp [hq]))]
        omega
  have hh := (hcard (hF.toFinset.card+1)).trans (Finset.card_le_card (hbound _))
  omega

theorem outside_bad {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hclosed : s.Closed) (hcovered : s.Covered)
    (ω : m.Config) (hfin : (Good q δ s ω).Finite)
    {x : Point} (hx : x ∈ Good q δ s ω) (d : Direction)
    (hy : x+outward d ∉ Good q δ s ω) : ω ∈ Bad q δ s (x+outward d) := by
  obtain ⟨N,hN⟩ := exists_empty_of_finite_good hs hcovered ω hfin
  have he := good_eq_of_empty q δ s ω hN
  have hxN : x ∈ (run q δ N s ω).good := by
    change x ∈ ((run q δ N s ω).good : Set Point)
    rwa [←he]
  have hv := run_closed q δ hclosed N ω x hxN d
  have hp : x+outward d ∈ (run q δ N s ω).processed := by
    simpa only [visited,hN,List.map_nil,List.toFinset_nil,Finset.union_empty] using hv
  rw [(run_colored hs hc N ω).partition,Finset.mem_union] at hp
  rcases hp with hg|hb
  · exact False.elim (hy ⟨N,hg⟩)
  · exact ⟨N,hb⟩

theorem hit_of_bad_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) (U : Finset Point)
    (hd : Disjoint U s.processed) (hU : U ⊆ (run q δ n s ω).bad) :
    ω ∈ (scheme (r := r) q δ).hit n s U := by
  induction n generalizing s U with
  | zero =>
    have he : U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
    rw [he,AdaptiveReveals.Scheme.hit_empty]
    trivial
  | succ n ih =>
    cases hq : s.queue with
    | nil =>
      have he : U = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        rw [run_empty q δ hq] at hU
        exact Finset.disjoint_left.mp hd hv (hc.bad_processed (hU hv))
      rw [he,AdaptiveReveals.Scheme.hit_empty]
      trivial
    | cons t ts =>
      have hchild : (scheme (r := r) q δ).child s (s.reveal.restrict ω) = s.advance q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.advance_determined q δ) ω).symm
      have hbad : (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = s.markedBad q δ ω :=
        (ProductCylinder.determinedBy_eq_extend (s.markedBad_determined q δ) ω).symm
      have hv : (scheme (r := r) q δ).vertex s = some t.vertex := by simp only [scheme,hq,List.head?_cons,Option.map_some]
      rw [AdaptiveReveals.Scheme.hit,hv]
      change (t.vertex ∈ U → (scheme (r := r) q δ).bad s (s.reveal.restrict ω) = true) ∧
        ω ∈ (scheme (r := r) q δ).hit n
          ((scheme (r := r) q δ).child s (s.reveal.restrict ω)) (U.erase t.vertex)
      rw [hchild,hbad]
      constructor
      · intro hv
        have hna : ¬s.Accept q δ t ω := by
          intro ha
          have hg : t.vertex ∈ (s.advance q δ ω).good := by
            simp only [advance,hq,ite_eq_left ha]; exact Finset.mem_insert_self _ _
          have hg' := run_good_mono q δ (s.advance q δ ω) ω (Nat.zero_le n) hg
          exact Finset.disjoint_left.mp (run_colored hs hc (n+1) ω).disjoint hg' (hU hv)
        simpa only [markedBad,hq,decide_eq_true_eq] using hna
      · apply ih (valid_advance hs ω) (colored_advance hs hc ω) (U.erase t.vertex)
        · apply Finset.disjoint_left.mpr
          intro v hv hp
          rw [advance_processed s q δ ω hq,Finset.mem_insert] at hp
          rcases hp with he|hp
          · exact (Finset.mem_erase.mp hv).1 he
          · exact Finset.disjoint_left.mp hd (Finset.mem_of_mem_erase hv) hp
        · exact Finset.Subset.trans (Finset.erase_subset _ _) hU

theorem exists_bad_time (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r)
    (ω : m.Config) (U : Finset Point) (hU : ∀ v ∈ U, ω ∈ Bad q δ s v) :
    ∃ n, U ⊆ (run q δ n s ω).bad := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0,Finset.empty_subset _⟩
  | @insert a U ha ih =>
    obtain ⟨k,hk⟩ := hU a (Finset.mem_insert_self _ _)
    obtain ⟨n,hn⟩ := ih (fun v hv => hU v (Finset.mem_insert_of_mem hv))
    refine ⟨max k n,?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact run_bad_mono q δ s ω (le_max_left _ _) hk
    · exact run_bad_mono q δ s ω (le_max_right _ _) (hn hv)

theorem bad_set_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    {ω | ∀ v ∈ U, ω ∈ Bad q δ s v} ⊆ ⋃ n, (scheme (r := r) q δ).hit n s U := by
  intro ω hω
  obtain ⟨n,hn⟩ := exists_bad_time q δ s ω U hω
  apply Set.mem_iUnion.mpr
  refine ⟨n,hit_of_bad_subset hs hc n ω U ?_ hn⟩
  apply Finset.disjoint_left.mpr
  intro v hv hp
  have hg : v ∈ s.good := by simpa only [hc.partition,hb,Finset.union_empty] using hp
  have hgn := run_good_mono q δ s ω (Nat.zero_le n) hg
  exact Finset.disjoint_left.mp (run_colored hs hc n ω).disjoint hgn (hn hv)

theorem bad_set_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | ∀ v ∈ U, ω ∈ Bad sc.q sc.δ s v} ≤ CriticalScales.contourError^U.card :=
  (measureReal_mono (bad_set_subset hs hc hb U)).trans (everHit_bound sc hs U)

theorem finite_good_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅)
    (hclosed : s.Closed) (hcovered : s.Covered) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | (Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Good sc.q sc.δ s ω} ≤ 25/144 := by
  apply PlanarBoundary.finite_good_bound _ (Good sc.q sc.δ s) (Bad sc.q sc.δ s)
    (fun ω hfin x hx d hy => outside_bad hs hc hclosed hcovered ω hfin hx d hy)
    (fun U => bad_set_bound sc hs hc hb U)

end Coarse.Exploration
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace LatticeGraph

theorem Subgraph.containsBox {G H : LatticeGraph} (h : G.Subgraph H) {B : Box}
    (hB : G.ContainsBox B) : H.ContainsBox B :=
  ⟨hB.1.trans h.1,hB.2.trans h.2⟩

theorem seedReaches_witness (G : LatticeGraph) (m : Model) {c : Vertex} {a b : ℕ}
    (hab : a ≤ b) (hB : G.ContainsBox (Box.cube c b)) {T : Set Vertex} {ω : m.Config}
    (hE : ω ∈ m.SeedReaches c a b T) :
    ∃ x y : G.Node, x.1 ∈ cube c a ∧ y.1 ∈ T ∧ G.Conn m ω x y := by
  obtain ⟨x,hxa,hxo,y,hy,hpath⟩ := hE
  have hxb := cube_mono c hab hxa
  have hyb : y ∈ cube c b := by
    induction hpath with
    | refl => exact hxb
    | tail _ hab _ => exact hab.2.1
  let x' : G.Node := ⟨x,G.containsBox_node hB (Box.contains_cube_iff.mpr hxb)⟩
  let y' : G.Node := ⟨y,G.containsBox_node hB (Box.contains_cube_iff.mpr hyb)⟩
  refine ⟨x',y',hxa,hy,(G.conn_iff m ω x' y').mpr ⟨?_,?_⟩⟩
  · cases m <;> exact hxo
  · apply G.lift_path (r := Within (cube c b) (m.BasicAdj ω)) ?_ ?_ hpath
    · intro x y h
      exact G.containsBox_node hB (Box.contains_cube_iff.mpr h.2.1)
    · intro x y h
      exact G.basicAdj_lift m hB (Box.contains_cube_iff.mpr h.1)
        (Box.contains_cube_iff.mpr h.2.1) h.2.2
end LatticeGraph

namespace Coarse

def facingFace (d : Direction) : FaceIndex :=
  (if d = 0 ∨ d = 2 then 1 else 0,fun _ => decide (d = 0 ∨ d = 3))

theorem facing_neighbor (r : ℕ) (d : Direction) {y : Vertex}
    (hy : y ∈ QuarterFace (center r (outward d)) (10*r) (facingFace d)) :
    ∃ z : Vertex, (Q r 0).Contains z ∧ NearestNeighbor z y := by
  have hQ := (quarterFace_subset_boundary _ _ _ hy).1
  rw [mem_cube] at hQ
  have h0 := hQ 0
  have h1 := hQ 1
  have h2 := hQ 2
  have hface := hy.1
  have hr : (0:ℤ) ≤ r := Int.natCast_nonneg _
  fin_cases d <;>
    simp [facingFace,center,outward,PlanarBoundary.outward] at hface h0 h1 h2
  · refine ⟨step y 1,?_,1,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega
  · let z := Function.update y 0 (y 0-1)
    refine ⟨z,?_,0,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 0
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · let z := Function.update y 1 (y 1-1)
    refine ⟨z,?_,1,Or.inl ?_⟩
    · intro i
      fin_cases i <;> simp [Q,Box.cube,center,z] <;> omega
    · ext i
      by_cases hi : i = 1
      · subst i; simp [z,step]
      · simp [z,step,hi,Ne.symm hi]
  · refine ⟨step y 0,?_,0,Or.inr rfl⟩
    intro i
    fin_cases i <;> simp [Q,Box.cube,center,step] <;> omega

noncomputable def rootPacket (r : ℕ) : Packet r where
  vertex := 0
  parent := 0
  graph := LatticeGraph.ofBox (Q r 0)
  contains := LatticeGraph.ofBox_contains _
  root_mem := (Box.mem_vertices _ _).mpr (zero_in_Q r)

noncomputable def initial (m : Model) (r : ℕ) : Exploration m r where
  history := ⟨rootBits m r,fun _ => true⟩
  processed := {0}
  queue := List.ofFn (fun d : Direction => (rootPacket r).child (outward d))
  good := {0}
  bad := ∅

theorem root_internal_disjoint (m : Model) (r : ℕ) (d : Direction) :
    Disjoint (rootBits m r) ((Q r (outward d)).bits m) := by
  rw [rootBits,Finset.disjoint_union_left]
  constructor
  · exact bits_disjoint m r (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 d))
  · apply Finset.disjoint_left.mpr
    intro e he hi
    obtain ⟨j,_,he⟩ := Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp
      (bits_link_disjoint m r (outward d) (Ne.symm (by simpa only [zero_add] using neighbor_ne 0 j))) hi he

theorem initial_seed_event (m : Model) (r a : ℕ) (ha : a ≤ 4*r) (d : Direction)
    {ω : m.Config} (hO : ω ∈ allValue (rootBits m r) true)
    (hE : ω ∈ m.SeedReaches (center r (outward d)) a (10*r)
      (QuarterFace (center r (outward d)) (10*r) (facingFace d))) :
    ω ∈ ((rootPacket r).child (outward d)).event m := by
  let t := (rootPacket r).child (outward d)
  let G := t.graph
  have hB : G.ContainsBox (Q r (outward d)) := t.contains
  have hroot : G.ContainsBox (Q r 0) :=
    (extendGraph_subgraph r (rootPacket r).graph 0 (outward d) (rootPacket r).contains).containsBox
      (rootPacket r).contains
  obtain ⟨x,y,hxa,hy,hxy⟩ := G.seedReaches_witness m (by omega) hB hE
  obtain ⟨z,hz,hzy⟩ := facing_neighbor r d hy
  let z' : G.Node := ⟨z,G.containsBox_node hroot hz⟩
  let o : G.Node := ⟨0,t.root_mem⟩
  have hrootOpen : ∀ e ∈ (Q r 0).bits m, ω e = true :=
    fun e he => hO e (Finset.mem_union_left _ he)
  have hoz : G.Conn m ω o z' := G.open_box_conn m hroot hrootOpen (zero_in_Q r) hz
  have hzy' : G.Adj m ω z' y := by
    obtain ⟨e,he⟩ := LatticeGraph.neighbor_incidence hzy
    have hi : e ∈ interface r 0 (outward d) := by
      rw [mem_interface]
      have hyQ : (Q r (outward d)).Contains y.1 :=
        Box.contains_cube_iff.mpr (quarterFace_subset_boundary _ _ _ hy).1
      rcases he with ⟨he0,he1⟩ | ⟨he0,he1⟩
      · exact Or.inl ⟨he0 ▸ hz,he1 ▸ hyQ⟩
      · exact Or.inr ⟨he0 ▸ hyQ,he1 ▸ hz⟩
    have hedge : e ∈ G.edges := Finset.mem_union_right _ hi
    cases m
    · exact ⟨e,hedge,he,hO e (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨d,Finset.mem_univ _,hi⟩))⟩
    · exact ⟨⟨e,hedge,he⟩,(G.conn_open .site hoz).2,(G.conn_open .site hxy).2⟩
  refine ⟨x,Box.contains_cube_iff.mpr (cube_mono _ ha hxa),?_⟩
  exact G.conn_trans m hoz (G.conn_trans m (G.conn_adj m hzy') (G.conn_symm m hxy))

theorem initial_promise {m : Model} (sc : ScaleData m) (d : Direction) :
    1-sc.δ < (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
      (((rootPacket sc.r).child (outward d)).event m) := by
  let E := m.SeedReaches (center sc.r (outward d)) sc.seed (10*sc.r)
    (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have ha : sc.seed ≤ 4*sc.r := by have := sc.seed_R; have := sc.large_r; omega
  have hdet := m.seedReaches_determined (center sc.r (outward d)) sc.seed (10*sc.r)
    (by omega) (QuarterFace (center sc.r (outward d)) (10*sc.r) (facingFace d))
  have heq : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E =
      (ProductCylinder.law (fun _ : m.Bit => sc.q)).real E :=
    fixed_determined_probability _ _ _ (root_internal_disjoint m sc.r d) _ _ hdet
  have hle : (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real E ≤
      (ProductCylinder.law ((initial m sc.r).history.parameter sc.q)).real
        (((rootPacket sc.r).child (outward d)).event m) := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    exact fun hE => initial_seed_event m sc.r sc.seed ha d hω hE
  have hh := sc.faces (10*sc.r) (by simp) (center sc.r (outward d)) (facingFace d)
  rw [heq] at hle
  exact (sub_lt_sub_left sc.γδ 1).trans (hh.trans_le hle)

@[simp] theorem mem_initial_queue (m : Model) (r : ℕ) (t : Packet r) :
    t ∈ (initial m r).queue ↔ ∃ d : Direction, (rootPacket r).child (outward d) = t := by
  simp only [initial,List.mem_ofFn]

theorem initial_valid {m : Model} (sc : ScaleData m) : (initial m sc.r).Valid sc.q sc.δ := by
  constructor
  · exact Finset.mem_singleton_self _
  · change ((List.ofFn (fun d : Direction => (rootPacket sc.r).child (outward d))).map Packet.vertex).Nodup
    rw [List.map_ofFn]
    exact List.nodup_ofFn.mpr outward_injective
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    simpa only [initial,Packet.child,Finset.mem_singleton,zero_add] using neighbor_ne 0 d
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Finset.mem_singleton_self _
  · intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    rw [Packet.child_bits]
    apply Finset.union_subset_union ?_ (Finset.Subset.refl _)
    change (LatticeGraph.ofBox (Q sc.r 0)).bits m ⊆ rootBits m sc.r
    have he : (LatticeGraph.ofBox (Q sc.r 0)).bits m = (Q sc.r 0).bits m := by cases m <;> rfl
    rw [he]
    exact Finset.subset_union_left
  · intro t ht
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact initial_promise sc d

theorem initial_colored (m : Model) (r : ℕ) : (initial m r).Colored := by
  constructor
  · simp only [initial,Finset.union_empty]
  · exact Finset.disjoint_empty_right _

theorem initial_closed (m : Model) (r : ℕ) : (initial m r).Closed := by
  intro v hv d
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  rw [zero_add]
  apply Exploration.queue_visited (initial m r) (t := (rootPacket r).child (outward d))
  exact (mem_initial_queue _ _ _).mpr ⟨d,rfl⟩

theorem initial_covered (m : Model) (r : ℕ) : (initial m r).Covered := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Or.inl hv
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Or.inr ⟨0,Finset.mem_singleton_self _,d,(zero_add _).symm⟩

end Coarse
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning.History
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem observe_pattern (h : History E) (R : Finset E) {ω : E → Bool}
    (hω : ω ∈ pattern h.known h.values) :
    ω ∈ pattern (h.observe R ω).known (h.observe R ω).values := by
  intro e he
  change ω e = replace R ω h.values e
  by_cases heR : e ∈ R
  · simp only [replace,ite_eq_left heR]
  · have heK : e ∈ h.known := (Finset.mem_union.mp he).resolve_right heR
    simpa only [replace,ite_eq_right heR] using hω e heK
end InfiniteConditioning.History

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

def Connected : (m : Model) → m.Config → Vertex → Vertex → Prop
  | .bond,ω,x,y => BondConnected ω x y
  | .site,ω,x,y => SiteConnected ω x y

def Cluster (m : Model) (ω : m.Config) (x : Vertex) : Set Vertex :=
  {y | m.Connected ω x y}

theorem infiniteAt_iff (m : Model) (ω : m.Config) (x : Vertex) :
    ω ∈ m.InfiniteAt x ↔ (m.Cluster ω x).Infinite := by cases m <;> rfl

theorem measurableSet_infiniteAt (m : Model) (x : Vertex) : MeasurableSet (m.InfiniteAt x) := by
  cases m
  · exact measurableSet_bondInfiniteAt x
  · exact measurableSet_siteInfiniteAt x
end Model

namespace LatticeGraph

theorem conn_global (G : LatticeGraph) (m : Model) {ω : m.Config} {x y : G.Node}
    (h : G.Conn m ω x y) : m.Connected ω x.1 y.1 := by
  cases m
  · exact G.bondConn_global h
  · exact G.siteConn_global h
end LatticeGraph

namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

def Sound (s : Exploration m r) (ω : m.Config) : Prop :=
  ∀ v ∈ s.good, ∃ y, (B r v).Contains y ∧ m.Connected ω 0 y

theorem accepted_event {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values)
    (ha : s.Accept q δ t ω) : ω ∈ t.event m := by
  have hh := (accept_current_iff hs hq ω).mp ha.1
  change s.history.freeze ω ∈ t.event m at hh
  simpa only [History.freeze,replace_eq_of_pattern hω] using hh

theorem sound_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) :
    (s.advance q δ ω).Sound ω := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · obtain ⟨y,hy,hpath⟩ := accepted_event hs hq hω ha
        exact ⟨y.1,hy,t.graph.conn_global m hpath⟩
      · exact hS v hv
    · exact hS v hv

theorem run_pattern (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values) (n : ℕ) :
    ω ∈ pattern (run q δ n s ω).history.known (run q δ n s ω).history.values := by
  induction n generalizing s with
  | zero => exact hω
  | succ n ih => exact ih (s.history.observe_pattern s.reveal hω)

theorem run_sound {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) (n : ℕ) :
    (run q δ n s ω).Sound ω := by
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    exact ih (valid_advance hs ω) (s.history.observe_pattern s.reveal hω)
      (sound_advance hs hω hS)

theorem good_finite_of_cluster_finite {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω)
    (hfin : (m.Cluster ω 0).Finite) : (Good q δ s ω).Finite := by
  have hf (y : Vertex) : ({v | (B r v).Contains y} : Set Point).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact cube_unique r (B_subset_Q r v y hv) (B_subset_Q r w y hw)
  apply (hfin.biUnion (fun y _ => hf y)).subset
  intro v hv
  obtain ⟨n,hn⟩ := hv
  obtain ⟨y,hy,hc⟩ := run_sound hs hω hS n v hn
  exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hc,hy⟩⟩
end Coarse.Exploration

namespace Coarse

theorem initial_sound (m : Model) (r : ℕ) {ω : m.Config}
    (hω : ω ∈ allValue (rootBits m r) true) : (initial m r).Sound ω := by
  intro v hv
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  refine ⟨0,?_,?_⟩
  · rw [B,center_zero]
    exact Box.center_mem_cube _ _
  · cases m
    · exact Relation.ReflTransGen.refl
    · refine ⟨hω 0 ?_,Relation.ReflTransGen.refl⟩
      apply Finset.mem_union_left
      exact (Box.mem_vertices _ _).mpr (zero_in_Q r)

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem scales_percolate {m : Model} (sc : ScaleData m) :
    0 < m.law (sc.q : ℝ) (m.InfiniteAt 0) := by
  let s := initial m sc.r
  let μ := ProductCylinder.law (s.history.parameter sc.q)
  let ν := ProductCylinder.law (fun _ : m.Bit => sc.q)
  have hs : s.Valid sc.q sc.δ := initial_valid sc
  have hb := Exploration.finite_good_bound sc hs (initial_colored m sc.r) rfl
    (initial_closed m sc.r) (initial_covered m sc.r)
  have hle : μ.real (m.InfiniteAt 0)ᶜ ≤ μ.real
      {ω | (Exploration.Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Exploration.Good sc.q sc.δ s ω} := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    intro hn
    have hfin : (m.Cluster ω 0).Finite := by
      by_contra hnf
      exact hn ((m.infiniteAt_iff ω 0).mpr hnf)
    exact ⟨Exploration.good_finite_of_cluster_finite hs hω (initial_sound m sc.r hω) hfin,
      Exploration.initial_good_subset sc.q sc.δ s ω (Finset.mem_singleton_self _)⟩
  have hpos : 0 < μ.real (m.InfiniteAt 0) := by
    rw [measureReal_compl (m.measurableSet_infiniteAt 0),probReal_univ] at hle
    dsimp [μ] at hle
    linarith
  let H := allValue (rootBits m sc.r) true
  have hH : 0 < ν.real H := by
    rw [show ν.real H = (sc.q : ℝ)^(rootBits m sc.r).card by
      exact allValue_probability_constant (fun _ : m.Bit => sc.q) (rootBits m sc.r)
        sc.q (fun _ _ => rfl) true]
    exact pow_pos sc.q_pos _
  have he : ν.real (H ∩ m.InfiniteAt 0) = ν.real H * μ.real (m.InfiniteAt 0) :=
    pattern_inter_real _ _ _ _ (m.measurableSet_infiniteAt 0)
  have hinf : 0 < ν.real (m.InfiniteAt 0) :=
    (he ▸ mul_pos hH hpos).trans_le (measureReal_mono Set.inter_subset_right)
  rw [m.law_coe_eq_product]
  exact ENNReal.toReal_pos_iff.mp hinf |>.1

/-- Positive percolation is open to the left throughout the open unit interval. -/
theorem lower_percolating_parameter (m : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < m.law p (m.InfiniteAt 0)) :
    ∃ q ∈ Set.Icc (0:ℝ) 1, q < p ∧ 0 < m.law q (m.InfiniteAt 0) := by
  obtain ⟨sc,hsc⟩ := exists_scales m hp hp1 hInf
  exact ⟨sc.q,sc.q.property,hsc ▸ sc.q_lt,scales_percolate sc⟩

end Coarse
end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace BlockPercolation
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
variable {E : Type}

def active (J : Point → Finset E) (ω : E → Bool) (v : Point) : Prop :=
  ∀ e ∈ J v, ω e = true

def Bad (J : Point → Finset E) (v : Point) : Set (E → Bool) :=
  {ω | ¬active J ω v}

def Adj (J : Point → Finset E) (ω : E → Bool) (x y : Point) : Prop :=
  (∃ d : Direction, y = x+outward d) ∧ active J ω x ∧ active J ω y

def cluster (J : Point → Finset E) (ω : E → Bool) : Set Point :=
  {v | active J ω (0,0) ∧ Relation.ReflTransGen (Adj J ω) (0,0) v}

theorem root_mem_iff (J : Point → Finset E) (ω : E → Bool) :
    (0,0) ∈ cluster J ω ↔ active J ω (0,0) :=
  ⟨And.left,fun h => ⟨h,.refl⟩⟩

theorem cluster_active {J : Point → Finset E} {ω : E → Bool} {v : Point}
    (hv : v ∈ cluster J ω) : active J ω v := by
  obtain ⟨h,hv⟩ := hv
  induction hv with
  | refl => exact h
  | tail _ hab _ => exact hab.2.2

theorem outside_bad (J : Point → Finset E) (ω : E → Bool) (x : Point)
    (hx : x ∈ cluster J ω) (d : Direction) (hy : x+outward d ∉ cluster J ω) :
    ω ∈ Bad J (x+outward d) := by
  intro ha
  exact hy ⟨hx.1,hx.2.tail ⟨⟨d,rfl⟩,cluster_active hx,ha⟩⟩

theorem bad_determined (J : Point → Finset E) (v : Point) :
    ProductCylinder.DeterminedBy (F := Prop) (J v) (fun ω => ω ∈ Bad J v) := by
  intro ω ω' h
  dsimp [Bad,active]
  congr 1
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_bad (J : Point → Finset E) (v : Point) : MeasurableSet (Bad J v) :=
  ProductCylinder.measurableSet_determined (J v) _
    (fun ω ω' h => eq_iff_iff.mp (bad_determined J v ω ω' h))

theorem single_closed_probability (p : Set.Icc (0 : ℝ) 1) (e : E) :
    (ProductCylinder.law (fun _ : E => p)).real {ω | ω e = false} = 1-(p : ℝ) := by
  have h := Measure.infinitePi_map_eval (fun _ : E => bernoulliMeasure true false p) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = false} = (fun ω => ω e) ⁻¹' {false} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun _ : E => bernoulliMeasure true false p)).map
    (fun ω => ω e) {false}).toReal = _
  rw [h]
  change (bernoulliMeasure true false p).real {false} = _
  rw [bernoulliMeasure_real_apply p (measurableSet_singleton _)]
  simp [unitInterval.coe_symm_eq]

theorem bad_probability_le (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E) (v : Point) :
    (ProductCylinder.law (fun _ : E => p)).real (Bad J v) ≤ (J v).card*(1-(p : ℝ)) := by
  have he : Bad J v = ⋃ e : J v, {ω | ω e.1 = false} := by
    ext ω
    simp only [Bad,active,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      push Not at h
      obtain ⟨e,he,hω⟩ := h
      exact ⟨⟨e,he⟩,Bool.eq_false_iff.mpr hω⟩
    · rintro ⟨e,he⟩ h
      have := h e.1 e.2
      simp_all
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  simp only [single_closed_probability,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,le_refl]

/-- Peierls survival for independent finite blocks of at most two bits. -/
theorem survival (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E)
    (hJ : Pairwise (fun u v => Disjoint (J u) (J v))) (hcard : ∀ v, (J v).card ≤ 2)
    (hp : 2*(1-(p : ℝ)) ≤ CriticalScales.contourError)
    (A : Set (E → Bool))
    (hA : ∀ ω, (cluster J ω).Infinite → ω ∈ A) :
    0 < ProductCylinder.law (fun _ : E => p) A := by
  let μ := ProductCylinder.law (fun _ : E => p)
  have hb (v : Point) : μ.real (Bad J v) ≤ CriticalScales.contourError := by
    apply (bad_probability_le p J v).trans
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (sub_nonneg.mpr p.2.2)).trans hp
  have hbad (s : Finset Point) : μ.real {ω | ∀ v ∈ s, ω ∈ Bad J v} ≤
      CriticalScales.contourError^s.card := by
    rw [InfiniteConditioning.disjoint_blocks_probability (fun _ : E => p) J hJ (Bad J) (bad_determined J) s]
    calc
      _ ≤ ∏ _v ∈ s, CriticalScales.contourError :=
        Finset.prod_le_prod (fun _ _ => measureReal_nonneg) (fun v _ => hb v)
      _ = _ := by simp
  have hf := PlanarBoundary.finite_good_bound μ (cluster J) (Bad J)
    (fun ω _ x hx d hy => outside_bad J ω x hx d hy) hbad
  have hroot : 1-CriticalScales.contourError ≤ μ.real {ω | active J ω (0,0)} := by
    have he : {ω | active J ω (0,0)} = (Bad J (0,0))ᶜ := by ext ω; simp [Bad]
    rw [he,measureReal_compl (measurableSet_bad J (0,0)),probReal_univ]
    linarith [hb (0,0)]
  have hcover : {ω | active J ω (0,0)} ⊆
      {ω | (cluster J ω).Finite ∧ (0,0) ∈ cluster J ω} ∪ A := by
    intro ω hω
    by_cases hfinite : (cluster J ω).Finite
    · exact Or.inl ⟨hfinite,(root_mem_iff J ω).mpr hω⟩
    · exact Or.inr (hA ω hfinite)
  have hle := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hpos : 0 < μ.real A := by
    have hh := CriticalScales.contourError_lt_half
    linarith
  exact ENNReal.toReal_pos_iff.mp hpos |>.1

end BlockPercolation

namespace CriticalZ3
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary

/-- The planar sublattice used only for the elementary strict upper threshold. -/
def planarEmbed (v : Point) : Vertex := ![v.1,v.2,0]

theorem planarEmbed_injective : Function.Injective planarEmbed := by
  intro u v h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact Prod.ext (by simpa [planarEmbed] using h0) (by simpa [planarEmbed] using h1)

@[simp] theorem planarEmbed_zero : planarEmbed (0,0) = 0 := by
  funext i; fin_cases i <;> rfl

def planarSiteBlock (v : Point) : Finset Vertex := {planarEmbed v}

def planarBondBlock (v : Point) : Finset Bond := {(planarEmbed v,0),(planarEmbed v,1)}

theorem planarSiteBlock_disjoint : Pairwise (fun u v => Disjoint (planarSiteBlock u) (planarSiteBlock v)) := by
  intro u v huv
  simp only [planarSiteBlock,Finset.disjoint_singleton]
  exact fun h => huv (planarEmbed_injective h)

theorem planarBondBlock_disjoint : Pairwise (fun u v => Disjoint (planarBondBlock u) (planarBondBlock v)) := by
  intro u v huv
  rw [Finset.disjoint_left]
  intro e he he'
  have hleft (w : Point) (he : e ∈ planarBondBlock w) : e.1 = planarEmbed w := by
    simp only [planarBondBlock,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> rfl
  exact huv (planarEmbed_injective ((hleft u he).symm.trans (hleft v he')))

theorem planarSiteBlock_card (v : Point) : (planarSiteBlock v).card ≤ 2 := by simp [planarSiteBlock]
theorem planarBondBlock_card (v : Point) : (planarBondBlock v).card ≤ 2 := by
  simp [planarBondBlock]

theorem planar_neighbor (v : Point) (d : Direction) :
    NearestNeighbor (planarEmbed v) (planarEmbed (v+outward d)) := by
  fin_cases d
  · refine ⟨1,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨1,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_site_open {ω : SiteConfig} {u v : Point}
    (h : BlockPercolation.Adj planarSiteBlock ω u v) :
    SiteOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  exact ⟨planar_neighbor u d,hu _ (Finset.mem_singleton_self _),hv _ (Finset.mem_singleton_self _)⟩

theorem planar_bond_open {ω : BondConfig} {u v : Point}
    (h : BlockPercolation.Adj planarBondBlock ω u v) :
    BondOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  have hu0 : ω (planarEmbed u,0) = true := hu _ (Finset.mem_insert_self _ _)
  have hu1 : ω (planarEmbed u,1) = true := hu _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv0 : ω (planarEmbed (u+outward d),0) = true := hv _ (Finset.mem_insert_self _ _)
  have hv1 : ω (planarEmbed (u+outward d),1) = true := hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  fin_cases d
  · refine Or.inr ⟨1,?_,hv1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨0,?_,hu0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨1,?_,hu1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inr ⟨0,?_,hv0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_bond_infinite {ω : BondConfig}
    (h : (BlockPercolation.cluster planarBondBlock ω).Infinite) : ω ∈ bondInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_bond_open h)
  change Relation.ReflTransGen (BondOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  rw [planarEmbed_zero] at hc
  exact hc

theorem planar_site_infinite {ω : SiteConfig}
    (h : (BlockPercolation.cluster planarSiteBlock ω).Infinite) : ω ∈ siteInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_site_open h)
  change Relation.ReflTransGen (SiteOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  refine ⟨?_,by simpa only [planarEmbed_zero] using hc⟩
  have ho := hv.1 (planarEmbed (0,0)) (Finset.mem_singleton_self _)
  simpa only [planarEmbed_zero] using ho

noncomputable def subunitParameter : Set.Icc (0 : ℝ) 1 :=
  ⟨1-CriticalScales.contourError/4,by
    have hf0 := CriticalScales.contourError_pos
    have hf1 := CriticalScales.contourError_lt_half
    constructor <;> linarith⟩

theorem subunitParameter_lt_one : (subunitParameter : ℝ) < 1 := by
  dsimp [subunitParameter]
  linarith [CriticalScales.contourError_pos]

theorem subunit_bond_positive : 0 < bondLaw subunitParameter (bondInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarBondBlock
    planarBondBlock_disjoint planarBondBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (bondInfiniteAt 0) (fun _ => planar_bond_infinite)
  simpa only [bondLaw,he,ProductCylinder.law] using h

theorem subunit_site_positive : 0 < siteLaw subunitParameter (siteInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarSiteBlock
    planarSiteBlock_disjoint planarSiteBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (siteInfiniteAt 0) (fun _ => planar_site_infinite)
  simpa only [siteLaw,he,ProductCylinder.law] using h

theorem bondCritical_lt_one : bondCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < bondLaw p (bondInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_bond_positive⟩) subunitParameter_lt_one

theorem siteCritical_lt_one : siteCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < siteLaw p (siteInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_site_positive⟩) subunitParameter_lt_one

end CriticalZ3

end OAI
end
end

section
section
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical

/-- Vanishing origin order parameter at the exact bond critical infimum. -/
theorem bond_critical_origin : bondLaw bondCritical (bondInfiniteAt 0) = 0 := by
  by_cases hc : bondCritical = 0
  · simp only [hc,bondLaw_zero_infinite]
  · have hp : 0 < bondCritical := lt_of_le_of_ne bondCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < bondLaw bondCritical (bondInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .bond hp bondCritical_lt_one hpos
    exact (ne_of_gt hqpos) (bond_subcritical_origin hq hqc)

/-- Vanishing origin order parameter at the separate site critical infimum. -/
theorem site_critical_origin : siteLaw siteCritical (siteInfiniteAt 0) = 0 := by
  by_cases hc : siteCritical = 0
  · simp only [hc,siteLaw_zero_infinite]
  · have hp : 0 < siteCritical := lt_of_le_of_ne siteCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < siteLaw siteCritical (siteInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .site hp siteCritical_lt_one hpos
    exact (ne_of_gt hqpos) (site_subcritical_origin hq hqc)

namespace SignedSymmetry

theorem bondConnected_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondConnected (fun e => ω (S.bond e)) x y ↔ BondConnected ω (S.vertex x) (S.vertex y) :=
  rtg_equiv_iff S.vertex (S.bondOpen_map ω) x y

theorem siteConnected_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteConnected (fun e => ω (S.vertex e)) x y ↔ SiteConnected ω (S.vertex x) (S.vertex y) :=
  and_congr_right (fun _ => rtg_equiv_iff S.vertex (S.siteOpen_map ω) x y)

theorem bondInfiniteAt_map (S : SignedSymmetry) (ω : BondConfig) (x : Vertex) :
    (fun e => ω (S.bond e)) ∈ bondInfiniteAt x ↔ ω ∈ bondInfiniteAt (S.vertex x) := by
  have he : bondCluster (fun e => ω (S.bond e)) x = S.vertex ⁻¹' bondCluster ω (S.vertex x) := by
    ext y
    exact S.bondConnected_map ω x y
  change (bondCluster (fun e => ω (S.bond e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)

theorem siteInfiniteAt_map (S : SignedSymmetry) (ω : SiteConfig) (x : Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteInfiniteAt x ↔ ω ∈ siteInfiniteAt (S.vertex x) := by
  have he : siteCluster (fun e => ω (S.vertex e)) x = S.vertex ⁻¹' siteCluster ω (S.vertex x) := by
    ext y
    exact S.siteConnected_map ω x y
  change (siteCluster (fun e => ω (S.vertex e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)
end SignedSymmetry

theorem bondInfiniteAt_probability (p : ℝ) (x : Vertex) :
    bondLaw p (bondInfiniteAt x) = bondLaw p (bondInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.bond e)) ⁻¹' bondInfiniteAt 0 = bondInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.bondInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.bond (parameter p) (bondInfiniteAt 0)
    (measurableSet_bondInfiniteAt 0)
  rw [he] at h
  exact h

theorem siteInfiniteAt_probability (p : ℝ) (x : Vertex) :
    siteLaw p (siteInfiniteAt x) = siteLaw p (siteInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.vertex e)) ⁻¹' siteInfiniteAt 0 = siteInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.siteInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.vertex (parameter p) (siteInfiniteAt 0)
    (measurableSet_siteInfiniteAt 0)
  rw [he] at h
  exact h

/-- Nearest-neighbor bond percolation on Z³ has almost surely no infinite cluster at criticality. -/
theorem bond_critical_no_infinite :
    ∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (bondInfiniteAt_probability bondCritical x).trans bond_critical_origin

/-- Nearest-neighbor site percolation on Z³ has almost surely no infinite cluster at its own criticality. -/
theorem site_critical_no_infinite :
    ∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (siteInfiniteAt_probability siteCritical x).trans site_critical_origin

theorem critical_no_infinite_oai :
    (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite) :=
  ⟨bond_critical_no_infinite, site_critical_no_infinite⟩

end CriticalZ3

end OAI
end
end

open MeasureTheory ProbabilityTheory in
theorem solution : type_of% @OAI.CriticalZ3.critical_no_infinite_oai := @OAI.CriticalZ3.critical_no_infinite_oai
