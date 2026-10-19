-- Prove2me | solution 1 for OAI.UniversalFInfinity.Cellular.contractible_of_sphereFillable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:52:46.78213+00:00
-- url     : https://prove2.me/submissions/d4efebaf-5634-4593-9259-bae6ca95c74d

import Mathlib
import Definitions.Def_OAIQWUFI006

section
-- module Solutions.OAIQW_UniversalFInfinity.CellularLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Topology BigOperators
open Set Metric Topology


namespace UniversalFInfinity.Cellular
universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X} [CWComplex C]

namespace PartialLift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}

lemma next_eq (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    {x : X} (hx : x ∈ Skeleton C n) : (a.next hp).val x = a.val x := by
  dsimp only [next]
  exact attachValue_old a.val _ hx

end PartialLift

section Lift
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))

lemma stages_agree {m n : ℕ} (h : m ≤ n) {x : X} (hx : x ∈ Skeleton C m) :
    (stages (C := C) hp f n).val x = (stages (C := C) hp f m).val x := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((stages (C := C) hp f n).next_eq hp (skeleton_mono hn hx)).trans ih

lemma liftValue_eq {n : ℕ} {x : X} (hx : x ∈ Skeleton C n) :
    liftValue (C := C) hp f x = (stages (C := C) hp f n).val x := by
  classical
  have hxC : x ∈ C := (CWComplex.skeletonLT C n).subset_complex hx
  rw [liftValue,dite_eq_left hxC]
  let m := (exists_skeleton (C := C) hxC).choose
  have hm : x ∈ Skeleton C m := (exists_skeleton (C := C) hxC).choose_spec
  exact (stages_agree hp f (Nat.le_max_left m n) hm).symm.trans
    (stages_agree hp f (Nat.le_max_right m n) hx)

lemma continuousOn_liftValue : ContinuousOn (liftValue (C := C) hp f) C := by
  apply (continuousOn_iff_characteristic _).2
  intro n i
  have hEq : liftValue (C := C) hp f ∘ characteristic n i =
      (stages (C := C) hp f (n+1)).val ∘ characteristic n i := by
    funext x
    exact liftValue_eq hp f (characteristic_mem_skeleton (Nat.lt_succ_self n) i x)
  rw [hEq]
  exact (stages (C := C) hp f (n+1)).continuousOn.comp_continuous (characteristic n i).continuous
    (characteristic_mem_skeleton (Nat.lt_succ_self n) i)

lemma liftValue_fac {x : X} (hx : x ∈ C) : p (liftValue (C := C) hp f x) = f x := by
  obtain ⟨n,hn⟩ := exists_skeleton (C := C) hx
  rw [liftValue_eq hp f hn]
  exact (stages (C := C) hp f n).fac x hn

include hp in

theorem exists_lift [CWComplex (Set.univ : Set X)] :
    ∃ g : C(X,E), ∀ x, p (g x) = f x := by
  refine ⟨⟨liftValue (C := Set.univ) hp f,
    continuousOn_univ.mp (continuousOn_liftValue (C := Set.univ) hp f)⟩,?_⟩
  intro x
  exact liftValue_fac hp f (Set.mem_univ x)

end Lift

noncomputable section

variable {Y : Type u} [TopologicalSpace Y]

theorem contractible_of_sphereFillable_oai {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [Nonempty Z] [CWComplex (Set.univ : Set Z)] (hZ : SphereFillable Z) :
    ContractibleSpace Z := by
  classical
  let z₀ : Z := Classical.choice ‹Nonempty Z›
  let : Nonempty C(unitInterval,Z) := ⟨ContinuousMap.const _ z₀⟩
  let f : C(Z,Z × Z) := ⟨fun z => (z,z₀),continuous_id.prodMk continuous_const⟩
  obtain ⟨g,hg⟩ := exists_lift (pathEndpoint_RLP hZ) f
  apply (contractible_iff_id_nullhomotopic Z).mpr
  refine ⟨z₀,⟨?_⟩⟩
  refine ContinuousMap.Homotopy.mk ⟨fun q => g q.2 q.1,
    continuous_eval.comp ((g.continuous.comp continuous_snd).prodMk continuous_fst)⟩ ?_ ?_
  · intro z
    exact congrArg Prod.fst (hg z)
  · intro z
    exact congrArg Prod.snd (hg z)

end
end UniversalFInfinity.Cellular

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalFInfinity.Cellular.contractible_of_sphereFillable_oai.{u} := @OAI.UniversalFInfinity.Cellular.contractible_of_sphereFillable_oai.{u}
