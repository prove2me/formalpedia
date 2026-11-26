-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.principalDivisor_apply
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:26:34.446815+00:00
-- url     : https://prove2.me/submissions/4a589950-7539-439d-b4f6-d7c039e34166

import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology
universe u
variable {X : Scheme.{u}}
variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
theorem _root_.solution (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    principalDivisor (Additive.ofMul f) x = x.ord (f : X.functionField) := by
  first
    | (intros; simp [PrimeDivisor, ord, principalDivisor])
    | (intros; unfold PrimeDivisor ord principalDivisor; simp)
    | (intros; simp [PrimeDivisor, ord, principalDivisor]; done)
    | (intros; ext; simp [PrimeDivisor, ord, principalDivisor])
    | (intros; simp only [PrimeDivisor, ord, principalDivisor]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [PrimeDivisor, ord, principalDivisor])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [PrimeDivisor, ord, principalDivisor])
    | (intros; unfold PrimeDivisor ord principalDivisor; split_ifs <;> simp_all)
    | (intros; unfold PrimeDivisor ord principalDivisor; positivity)
    | (intros; unfold PrimeDivisor ord principalDivisor; ring)
    | (intros; unfold PrimeDivisor ord principalDivisor; exact?)
    | (intros; aesop (add norm simp [PrimeDivisor, ord, principalDivisor]))
    | (intros; simp [PrimeDivisor, ord, principalDivisor] <;> aesop)
    | (intros; exact PrimeDivisor.symm ..)
    | (intros; exact PrimeDivisor.comm ..)
    | (intros; exact ord.symm ..)
    | (intros; exact ord.comm ..)
  trace "HIT_183_0"

