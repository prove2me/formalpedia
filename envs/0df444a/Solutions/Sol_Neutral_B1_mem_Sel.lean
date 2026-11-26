-- Prove2me | solution 1 for Neutral.B1.mem_Sel
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:14:24.382869+00:00
-- url     : https://prove2.me/submissions/59a05f57-e989-4085-af49-dd5fe678adf0

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation
open Neutral Neutral.B1
noncomputable section
open Representation
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable (rho : Representation R G M)
variable {I : Type*} {D : I → Type*} [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  (phi : ∀ i, D i →* G) (hphi : ∀ i, Continuous (phi i))
theorem _root_.solution (L : LocCond rho phi) (x : H1 rho) :
    x ∈ Sel rho phi hphi L ↔ ∀ i, resH1 rho (phi i) (hphi i) x ∈ L i := by
  first
    | (intros; simp [H1, resH1, LocCond, Sel])
    | (intros; unfold H1 resH1 LocCond Sel; simp)
    | (intros; simp [H1, resH1, LocCond, Sel]; done)
    | (intros; ext; simp [H1, resH1, LocCond, Sel])
    | (intros; simp only [H1, resH1, LocCond, Sel]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [H1, resH1, LocCond, Sel])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [H1, resH1, LocCond, Sel])
    | (intros; unfold H1 resH1 LocCond Sel; split_ifs <;> simp_all)
    | (intros; unfold H1 resH1 LocCond Sel; positivity)
    | (intros; unfold H1 resH1 LocCond Sel; ring)
    | (intros; unfold H1 resH1 LocCond Sel; exact?)
    | (intros; aesop (add norm simp [H1, resH1, LocCond, Sel]))
    | (intros; simp [H1, resH1, LocCond, Sel] <;> aesop)
    | (intros; exact H1.symm ..)
    | (intros; exact H1.comm ..)
    | (intros; exact resH1.symm ..)
    | (intros; exact resH1.comm ..)
  trace "HIT_28_6"

end 
end 
