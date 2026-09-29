-- Prove2me | solution 1 for ModularCurve.FullLevel.igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/0666b06f-9368-5179-b031-f34bf6ab9308

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_AlgebraicCurve_SemilinearAut_mem_iff_smul_mem_of_forall_mem_iff_sections
import Theorems.Thm_ModularCurve_FullLevel_arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd

section Inlined_w1_W1c_tube_penw2

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ SemistableCovering.NaturalityClauses SemistableCovering.InducesOnChart SemistableCovering.LevelPinClauses arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace W1c
namespace Plumbing
p2m_open "ModularCurve.FullLevel ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in

def InTube (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) : Prop :=
  ∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
            0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
          (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
              (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
            ∀ a : A, residue A a =
                (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
              ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                (⟨_, h⟩ : A) ∈ maximalIdeal A

def jBar (M' : ℕ) [NeZero M'] : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩

def jNBar (M' : ℕ) [NeZero M'] : ↥(modularFunctionFieldBar M') :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩

@[scoped simp] theorem coe_jBar (M' : ℕ) [NeZero M'] :
    ((jBar M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) jq := rfl

@[scoped simp] theorem coe_jNBar (M' : ℕ) [NeZero M'] :
    ((jNBar M' : ↥(modularFunctionFieldBar M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq) := rfl

set_option synthInstance.maxHeartbeats 1600000 in

def InTubeJ (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')) (P : Place (AlgebraicClosure ℚ) (fieldBar q M')) : Prop :=
  ((IntermediateField.inclusion hle (jBar M') : fieldBar q M') ∈ P.toValuationSubring ∧
    ∀ a : A, residue A a = s.evalAt (jGeomGen (ResidueField A) M') →
      ∃ h : P.evalAt (IntermediateField.inclusion hle (jBar M') : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
        (⟨_, h⟩ : A) ∈ maximalIdeal A) ∧
  ((IntermediateField.inclusion hle (jNBar M') : fieldBar q M') ∈ P.toValuationSubring ∧
    ∀ a : A, residue A a = s.evalAt (jNGeomGen (ResidueField A) M') →
      ∃ h : P.evalAt (IntermediateField.inclusion hle (jNBar M') : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
        (⟨_, h⟩ : A) ∈ maximalIdeal A)

namespace Idx

private def _root_.ModularCurve.FullLevel.W1c.Plumbing.Idx.unit {q : ℕ} [Fact q.Prime] (ζ : Idx q) : (AlgebraicClosure ℚ)ˣ :=
  (ζ.isPrimitiveRoot.isUnit (Fact.out : q.Prime).ne_zero).unit

end Idx
p2m_export "ModularCurve.FullLevel.W1c.Plumbing" "Idx.unit"
@[scoped simp] theorem Idx.coe_unit {q : ℕ} [Fact q.Prime] (ζ : Idx q) : (Idx.unit ζ : AlgebraicClosure ℚ) = ζ.val := rfl

p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx"
end ModularCurve.FullLevel.W1c.Plumbing
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_W1c_tube_penw2
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_pen_LevelPin_pen

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ SemistableCovering.NaturalityClauses SemistableCovering.InducesOnChart SemistableCovering.LevelPinClauses arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem mem_maximalIdeal_of_valuationSubring_eq {F : Type*} [Field F] {O₁ O₂ : ValuationSubring F}
    (e : O₁ = O₂) {x : F} (h₁ : x ∈ O₁) (h₂ : x ∈ O₂) (hm : (⟨x, h₁⟩ : O₁) ∈ maximalIdeal ↥O₁) :
    (⟨x, h₂⟩ : O₂) ∈ maximalIdeal ↥O₂ := by
  subst e; exact hm

set_option synthInstance.maxHeartbeats 1600000 in

theorem levelPin_ss_of_integers_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (s : ↥W) {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (C : ComponentChart A (fieldBar q M') FSS) (hCint : C.integers = OSS s)
    (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers)
    (hreg : ∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M')))
    (hs : (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring) :
    ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers,
      C.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
        ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩)) := by
  obtain ⟨hO, hmax⟩ := hSS_over s f hf hreg hs
  have hCf : (IntermediateField.inclusion hle f : fieldBar q M') ∈ C.integers := by rw [hCint]; exact hO
  refine ⟨hCf, ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal ↥A)
    ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩))
  have ha' : residue A a =
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) := ha
  obtain ⟨hsub, hmx⟩ := hmax a ha'
  have haC : algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C.integers :=
    (C.algebraMap_mem_iff a).mpr a.2
  have hsubC : (IntermediateField.inclusion hle f : fieldBar q M')
      - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ C.integers :=
    C.integers.toSubring.sub_mem hCf haC
  have hmxC : (⟨_, hsubC⟩ : C.integers) ∈ maximalIdeal ↥C.integers :=
    mem_maximalIdeal_of_valuationSubring_eq hCint.symm hsub hsubC hmx
  rw [← C.ker_residue, RingHom.mem_ker] at hmxC
  have hsplit : (⟨_, hsubC⟩ : C.integers) = ⟨_, hCf⟩ - ⟨_, haC⟩ := Subtype.ext rfl
  rw [hsplit, map_sub, C.residue_algebraMap a, sub_eq_zero] at hmxC
  rw [hmxC, ha']

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_pen_LevelPin_pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_W1c_spec

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ SemistableCovering.NaturalityClauses SemistableCovering.InducesOnChart SemistableCovering.LevelPinClauses arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace W1c
p2m_open "ModularCurve.FullLevel ModularCurve"

section Spec

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

set_option synthInstance.maxHeartbeats 1600000 in

def LevelAuts : Subgroup ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')) :=
  Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}

set_option synthInstance.maxHeartbeats 1600000 in
theorem levelAutBar_mem_levelAuts (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') :
    levelAutBar q M' ζ γ ∈ LevelAuts q M' :=
  Subgroup.subset_closure ⟨ζ, γ, hγ, rfl⟩

end Spec
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

@[reducible] private def _root_.AlgebraicCurve.ComponentChart.toRegularProlongation
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

p2m_alias "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.AlgebraicCurve.ComponentChart.toRegularProlongation" "AlgebraicCurve.ComponentChart.toRegularProlongation"
end ModularCurve.FullLevel.W1c
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_W1c_spec
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_pen_NatPlumbing_pen

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ SemistableCovering.NaturalityClauses SemistableCovering.InducesOnChart SemistableCovering.LevelPinClauses arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

theorem ofAlgAut_smul_place {K F : Type*} [Field K] [Field F] [Algebra K F] (φ : F ≃ₐ[K] F) (Q : Place K F) :
    SemilinearAut.ofAlgAut φ • Q = φ • Q := by
  ext1
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    SemilinearAut.inv_smul_def, SemilinearAut.toRingAut_ofAlgAut, AlgEquiv.smul_def, AlgEquiv.aut_inv]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in

theorem chartClauses_of_discFamily_semilinear
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A (fieldBar q M') Fbar) (N : Finset (Place (ResidueField A) Fbar))
    (disc : Place (ResidueField A) Fbar → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (C : ComponentChart A (fieldBar q M') Fbar)
    (hint : C.integers = R.integers)
    (hres : ∀ (f : fieldBar q M') (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)
    (hdom : ∀ P, P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q)
    (hpm : ∀ P Q, Q ∉ N → P ∈ disc Q → C.placeMap P = Q)
    (g : SemilinearAut (AlgebraicClosure ℚ) (fieldBar q M'))
    (hst : ∀ f : fieldBar q M', f ∈ R.integers ↔ g • f ∈ R.integers)
    (φ : Fbar ≃ₐ[ResidueField A] Fbar)
    (hφ : ∀ (f : fieldBar q M') (hf : f ∈ R.integers), R.residue ⟨g • f, (hst f).mp hf⟩ = φ (R.residue ⟨f, hf⟩))
    (hN : ∀ Q, φ • Q ∈ N ↔ Q ∈ N)
    (hD : ∀ Q, Q ∉ N → ∀ P, g • P ∈ disc (φ • Q) ↔ P ∈ disc Q) :
    (∀ f : fieldBar q M', f ∈ C.integers ↔ g • f ∈ C.integers) ∧
    (∀ P, P ∈ C.dom ↔ g • P ∈ C.dom) ∧
    SemistableCovering.InducesOnChart C g φ.toRingEquiv ∧
    (∀ P ∈ C.dom, C.placeMap (g • P) = SemilinearAut.ofAlgAut φ • C.placeMap P) := by
  have h1 : ∀ f : fieldBar q M', f ∈ C.integers ↔ g • f ∈ C.integers := fun f => by
    rw [hint]; exact hst f
  have h2 : ∀ P, P ∈ C.dom ↔ g • P ∈ C.dom := fun P => by
    rw [hdom, hdom]
    constructor
    · rintro ⟨Q, hQ, hP⟩
      exact ⟨φ • Q, fun h => hQ ((hN Q).mp h), (hD Q hQ P).mpr hP⟩
    · rintro ⟨Q', hQ', hP'⟩
      refine ⟨φ⁻¹ • Q', fun h => hQ' ?_, (hD (φ⁻¹ • Q') (fun h => hQ' ?_) P).mp ?_⟩
      · rwa [← hN, smul_inv_smul] at h
      · rwa [← hN, smul_inv_smul] at h
      · rwa [smul_inv_smul]
  refine ⟨h1, h2, ⟨h1, fun f hf => ?_⟩, fun P hP => ?_⟩
  · have hR : f ∈ R.integers := hint ▸ hf
    rw [hres _ _ ((hst f).mp hR), hres _ hf hR, hφ f hR]
    rfl
  · obtain ⟨Q, hQ, hPQ⟩ := (hdom P).mp hP
    rw [hpm P Q hQ hPQ, ofAlgAut_smul_place,
      hpm (g • P) (φ • Q) (fun h => hQ ((hN Q).mp h)) ((hD Q hQ P).mpr hPQ)]

set_option synthInstance.maxHeartbeats 1600000 in

theorem naturality_b_of_discFamily
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {FSS : Type} [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS) (O : ValuationSubring (fieldBar q M')) (hRb : R.integers = O)
    (hfix : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → O.comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = O)
    (xt : CuspidalType.ProjLine q → Place (ResidueField A) FSS)
    (disc : Place (ResidueField A) FSS → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (hxt_stab : ∀ τ ∈ Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers)
        (Q : Place (ResidueField A) FSS), R.resAut τ hτ • Q ∈ Set.range xt ↔ Q ∈ Set.range xt)
    (hdisc_stab : ∀ τ ∈ Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
        ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers)
        (Q : Place (ResidueField A) FSS), Q ∉ Set.range xt →
          RegularProlongation.smulDisc τ (disc Q) = disc (R.resAut τ hτ • Q))
    (C : ComponentChart A (fieldBar q M') FSS)
    (hint : C.integers = R.integers)
    (hres : ∀ (f : fieldBar q M') (hC : f ∈ C.integers) (hR : f ∈ R.integers), C.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)
    (hdom : ∀ P, P ∈ C.dom ↔ ∃ Q, Q ∉ Set.range xt ∧ P ∈ disc Q)
    (hpm : ∀ P Q, Q ∉ Set.range xt → P ∈ disc Q → C.placeMap P = Q)
    (ζ : Idx q) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M') :
    ∃ φ : FSS ≃ₐ[ResidueField A] FSS,
      SemistableCovering.InducesOnChart C (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹)) φ.toRingEquiv ∧
      ∀ P ∈ C.dom, C.placeMap (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ⁻¹) • P) =
        SemilinearAut.ofAlgAut φ • C.placeMap P := by
  classical
  set τ : (fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M') := levelAutBar q M' ζ γ⁻¹ with hτdef
  have hγ' : γ⁻¹ ∈ Gamma0 M' := Subgroup.inv_mem _ hγ
  have hτmem : τ ∈ Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ} :=
    Subgroup.subset_closure ⟨ζ, γ⁻¹, hγ', rfl⟩
  have hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers := fun f => by
    have e := SetLike.ext_iff.mp (hfix ζ γ⁻¹ hγ') f
    rw [hRb]
    exact e
  have hst : ∀ f : fieldBar q M', f ∈ R.integers ↔ SemilinearAut.ofAlgAut τ • f ∈ R.integers := fun f => by
    rw [SemilinearAut.ofAlgAut_smul]; exact (hτ f).symm

  let N : Finset (Place (ResidueField A) FSS) := (Set.finite_range xt).toFinset
  have hN_iff : ∀ Q, Q ∈ N ↔ Q ∈ Set.range xt := fun Q => Set.Finite.mem_toFinset _
  have hdom' : ∀ P, P ∈ C.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q := fun P => by
    rw [hdom]; simp only [hN_iff]
  have hpm' : ∀ P Q, Q ∉ N → P ∈ disc Q → C.placeMap P = Q := fun P Q hQ hP =>
    hpm P Q (fun h => hQ ((hN_iff Q).mpr h)) hP
  have hφ : ∀ (f : fieldBar q M') (hf : f ∈ R.integers),
      R.residue ⟨SemilinearAut.ofAlgAut τ • f, (hst f).mp hf⟩ = R.resAut τ hτ (R.residue ⟨f, hf⟩) := fun f hf => by
    rw [RegularProlongation.resAut_residue]
    rfl
  have hN : ∀ Q, R.resAut τ hτ • Q ∈ N ↔ Q ∈ N := fun Q => by
    rw [hN_iff, hN_iff]; exact hxt_stab τ hτmem hτ Q
  have hD : ∀ Q, Q ∉ N → ∀ P, SemilinearAut.ofAlgAut τ • P ∈ disc (R.resAut τ hτ • Q) ↔ P ∈ disc Q := by
    intro Q hQ P
    rw [ofAlgAut_smul_place, ← hdisc_stab τ hτmem hτ Q (fun h => hQ ((hN_iff Q).mpr h)),
      RegularProlongation.smul_mem_smulDisc_iff]
  obtain ⟨-, -, hind, hplace⟩ :=
    chartClauses_of_discFamily_semilinear R N disc C hint hres hdom' hpm' (SemilinearAut.ofAlgAut τ) hst
      (R.resAut τ hτ) hφ hN hD
  exact ⟨R.resAut τ hτ, hind, hplace⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem naturality_c_of_discFamily
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A (fieldBar q M') Fbar) (N : Finset (Place (ResidueField A) Fbar))
    (disc : Place (ResidueField A) Fbar → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (S : Subgroup ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hNstab : ∀ τ ∈ S, ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers)
      (Q : Place (ResidueField A) Fbar), R.resAut τ hτ • Q ∈ N ↔ Q ∈ N)
    (hdiscstab : ∀ τ ∈ S, ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers)
      (Q : Place (ResidueField A) Fbar), Q ∉ N → RegularProlongation.smulDisc τ (disc Q) = disc (R.resAut τ hτ • Q))
    (C₀ : ComponentChart A (fieldBar q M') Fbar)
    (hint : C₀.integers = R.integers)
    (hres : ∀ (f : fieldBar q M') (hC : f ∈ C₀.integers) (hR : f ∈ R.integers), C₀.residue ⟨f, hC⟩ = R.residue ⟨f, hR⟩)
    (hdom : ∀ P, P ∈ C₀.dom ↔ ∃ Q, Q ∉ N ∧ P ∈ disc Q)
    (hpm : ∀ P Q, Q ∉ N → P ∈ disc Q → C₀.placeMap P = Q)
    (σ : (fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')) (hσ : σ ∈ S)
    (hσR : ∀ f : (fieldBar q M'), σ f ∈ R.integers ↔ f ∈ R.integers)
    (τ : (fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')) (hτS : τ ∈ S)
    (hind : SemistableCovering.InducesOnChart (C₀.comap σ) (SemilinearAut.ofAlgAut τ) (RingEquiv.refl _)) :
    (∀ P, P ∈ (C₀.comap σ).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (C₀.comap σ).dom) ∧
    (∀ P ∈ (C₀.comap σ).dom, (C₀.comap σ).placeMap (SemilinearAut.ofAlgAut τ • P) = (C₀.comap σ).placeMap P) := by
  unfold SemistableCovering.InducesOnChart at hind
  obtain ⟨hst, hresid⟩ := hind

  set τ' : (fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M') := σ * τ * σ⁻¹ with hτ'def
  have hτ'S : τ' ∈ S := Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hτS) (Subgroup.inv_mem _ hσ)
  have hτ'app : ∀ f : fieldBar q M', τ' f = σ (τ (σ⁻¹ f)) := fun f => rfl
  have hmemC : ∀ f : fieldBar q M', σ⁻¹ f ∈ (C₀.comap σ).integers ↔ f ∈ R.integers := fun f => by
    rw [ComponentChart.mem_comap_integers, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hint]
  have hτ'R : ∀ f : (fieldBar q M'), τ' f ∈ R.integers ↔ f ∈ R.integers := fun f => by
    have e := hst (σ⁻¹ f)
    rw [SemilinearAut.ofAlgAut_smul, hmemC, ComponentChart.mem_comap_integers, hint] at e
    rw [hτ'app]
    exact e.symm
  have hres' : ∀ (f : fieldBar q M') (hf : f ∈ R.integers),
      R.residue ⟨τ' f, (hτ'R f).mpr hf⟩ = R.residue ⟨f, hf⟩ := by
    intro f hf
    have hf₀ : σ⁻¹ f ∈ (C₀.comap σ).integers := (hmemC f).mpr hf
    have e := hresid (σ⁻¹ f) hf₀
    rw [RingEquiv.refl_apply, ComponentChart.comap_residue_apply, ComponentChart.comap_residue_apply] at e

    have h1 : σ (σ⁻¹ f) = f := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    have hR1 : σ (SemilinearAut.ofAlgAut τ • σ⁻¹ f) ∈ R.integers := by
      rw [SemilinearAut.ofAlgAut_smul, ← hτ'app]; exact (hτ'R f).mpr hf
    have hR2 : σ (σ⁻¹ f) ∈ R.integers := by rw [h1]; exact hf
    rw [hres _ _ hR1, hres _ _ hR2] at e
    have e1 : R.residue ⟨τ' f, (hτ'R f).mpr hf⟩ = R.residue ⟨σ (SemilinearAut.ofAlgAut τ • σ⁻¹ f), hR1⟩ := by
      congr 1
    have e2 : R.residue ⟨f, hf⟩ = R.residue ⟨σ (σ⁻¹ f), hR2⟩ := by
      congr 1; exact Subtype.ext h1.symm
    exact e1.trans (e.trans e2.symm)
  have hres1 : R.resAut τ' hτ'R = 1 := by
    ext x
    obtain ⟨f, rfl⟩ := R.residue_surjective x
    rw [RegularProlongation.resAut_residue, AlgEquiv.one_apply]
    exact hres' f f.2

  have hst₀ : ∀ f : fieldBar q M', f ∈ R.integers ↔ SemilinearAut.ofAlgAut τ' • f ∈ R.integers := fun f => by
    rw [SemilinearAut.ofAlgAut_smul]; exact (hτ'R f).symm
  have hφ : ∀ (f : fieldBar q M') (hf : f ∈ R.integers),
      R.residue ⟨SemilinearAut.ofAlgAut τ' • f, (hst₀ f).mp hf⟩ = R.resAut τ' hτ'R (R.residue ⟨f, hf⟩) := fun f hf => by
    rw [RegularProlongation.resAut_residue]; rfl
  have hD : ∀ Q, Q ∉ N → ∀ P, SemilinearAut.ofAlgAut τ' • P ∈ disc (R.resAut τ' hτ'R • Q) ↔ P ∈ disc Q := by
    intro Q hQ P
    rw [ofAlgAut_smul_place, ← hdiscstab τ' hτ'S hτ'R Q hQ, RegularProlongation.smul_mem_smulDisc_iff]
  obtain ⟨-, hdom₀, -, hplace₀⟩ :=
    chartClauses_of_discFamily_semilinear R N disc C₀ hint hres hdom hpm (SemilinearAut.ofAlgAut τ') hst₀
      (R.resAut τ' hτ'R) hφ (hNstab τ' hτ'S hτ'R) hD
  have hcomm : ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), σ • (τ • P) = τ' • (σ • P) := fun P => by
    rw [hτ'def, mul_smul, mul_smul, inv_smul_smul]
  refine ⟨fun P => ?_, fun P hP => ?_⟩
  · rw [ComponentChart.mem_comap_dom, ComponentChart.mem_comap_dom, ofAlgAut_smul_place, hcomm, ← ofAlgAut_smul_place]
    exact hdom₀ (σ • P)
  · rw [ComponentChart.comap_placeMap, ComponentChart.comap_placeMap, ofAlgAut_smul_place, hcomm, ← ofAlgAut_smul_place,
      hplace₀ (σ • P) hP, ofAlgAut_smul_place, hres1, one_smul]

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_pen_NatPlumbing_pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_w1_pen_InertiaUnpack_pen

set_option autoImplicit false

noncomputable section

open IsLocalRing
open scoped Pointwise

namespace ValuationSubring
p2m_export "ValuationSubring" "comap subtype smul_mem_pointwise_smul_iff inertiaSubgroup toSubring ext smul_mem_pointwise_smul mul_mem mem_pointwise_smul_iff_inv_smul_mem decompositionSubgroup algebra valuation inclusion LiesOverPrime inertiaSubgroupIn tameCharacter"
p2m_open "ValuationSubring"

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

private theorem _root_.ValuationSubring.mem_iff_of_mem_inertiaSubgroupIn {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K) (x : L) :
    τ x ∈ A ↔ x ∈ A := by
  obtain ⟨d, -, rfl⟩ := Subgroup.mem_map.mp hτ
  have hd : (d : L ≃ₐ[K] L) • A = A := d.prop
  constructor
  · intro h
    have h' : (d : L ≃ₐ[K] L) • x ∈ (d : L ≃ₐ[K] L) • A := by rw [hd]; exact h
    exact smul_mem_pointwise_smul_iff.mp h'
  · intro h
    have h' : (d : L ≃ₐ[K] L) • x ∈ (d : L ≃ₐ[K] L) • A := smul_mem_pointwise_smul _ _ _ h
    rwa [hd] at h'

p2m_export "ValuationSubring" "mem_iff_of_mem_inertiaSubgroupIn"
private theorem _root_.ValuationSubring.residue_apply_of_mem_inertiaSubgroupIn {τ : L ≃ₐ[K] L} (hτ : τ ∈ A.inertiaSubgroupIn K) (a : A) :
    IsLocalRing.residue A ⟨τ a, (A.mem_iff_of_mem_inertiaSubgroupIn hτ a).mpr a.2⟩ = IsLocalRing.residue A a := by
  obtain ⟨d, hdI, hdτ⟩ := Subgroup.mem_map.mp hτ
  have hker : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) d = 1 :=
    (MonoidHom.mem_ker).mp hdI
  have h1 : d • IsLocalRing.residue A a = IsLocalRing.residue A a := by
    have := RingEquiv.congr_fun hker (IsLocalRing.residue A a)
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h1
  rw [← h1]
  congr 1
  apply Subtype.ext
  show τ a = ((d • a : A) : L)
  subst hdτ
  rfl

p2m_export "ValuationSubring" "residue_apply_of_mem_inertiaSubgroupIn"
end ValuationSubring
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
p2m_open "ModularCurve"

variable {L : Type*} [Field L] [Algebra ℚ L] (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (A : ValuationSubring L)

theorem baseAut_arithmeticGalois_mem_iff {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (x : L) :
    AlgebraicCurve.SemilinearAut.baseAut (arithmeticGalois F₀ τ) x ∈ A ↔ x ∈ A := by
  rw [baseAut_arithmeticGalois]
  exact A.mem_iff_of_mem_inertiaSubgroupIn hτ x

theorem residue_baseAut_arithmeticGalois {τ : L ≃ₐ[ℚ] L} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (a : A) :
    IsLocalRing.residue A ⟨AlgebraicCurve.SemilinearAut.baseAut (arithmeticGalois F₀ τ) a,
        (baseAut_arithmeticGalois_mem_iff F₀ A hτ a).mpr a.2⟩ = IsLocalRing.residue A a := by
  have := A.residue_apply_of_mem_inertiaSubgroupIn hτ a
  rw [← this]
  congr 1

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_w1_pen_InertiaUnpack_pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

section Inlined_MAIN

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "xHFunctionFieldC xHFunctionField arithmeticGalois baseAut_arithmeticGalois modularFunctionFieldBar qExpand jq jq_mem jqN_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange instDecidableEqResidueFieldSemistable instAlgebraResidueFieldModularFunctionFieldCSemistable modularFunctionFieldC ssPlaces jGeomGen jNGeomGen FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty SemistableCovering levelH fieldBar Idx IsLevelAutBar levelAutBar redQ SemistableCovering.NaturalityClauses SemistableCovering.InducesOnChart SemistableCovering.LevelPinClauses arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one"
namespace W1c
namespace Pen
p2m_open "ModularCurve.FullLevel ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem ig_semilinear_leaf_proof
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (CIg : CuspidalType.ProjLine q → ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (Cinf : ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (RI : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hRI : RI.integers = OIg (lineInfty q))
    (hCinfint : Cinf.integers = RI.integers)
    (hCinfres : ∀ (f : fieldBar q M') (hC : f ∈ Cinf.integers) (hR : f ∈ RI.integers), Cinf.residue ⟨f, hC⟩ = RI.residue ⟨f, hR⟩)
    (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
    (discI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (coordI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
    (hnodesI : Cinf.nodes = NIg) (hfamI : RI.DiscFamily NIg discI coordI)
    (SI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
    (χ₀I : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(SI Q) →+* ResidueField A)
    (hstalkI : (∀ Q, Q ∉ NIg → (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ RI.integers) ∧
        ∀ P, P ∈ discI Q ↔ P.IsRational ∧
          (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(SI Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀I Q f = 0)))
    (hdomI : ∀ P, P ∈ Cinf.dom ↔ ∃ Q, Q ∉ NIg ∧ P ∈ discI Q)
    (hpmI : ∀ P Q, Q ∉ NIg → P ∈ discI Q → Cinf.placeMap P = Q)
    (hpmI_off : ∀ P P', P ∉ Cinf.dom → P' ∉ Cinf.dom → Cinf.placeMap P = Cinf.placeMap P')
    (hNstabI : ∀ τ ∈ LevelAuts q M', ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), RI.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg)
    (hdiscstabI : ∀ τ ∈ LevelAuts q M', ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), Q ∉ NIg → RegularProlongation.smulDisc τ (discI Q) = discI (RI.resAut τ hτ • Q))
    (g : CuspidalType.ProjLine q → ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hg : ∀ ℓ, g ℓ ∈ LevelAuts q M' ∧ ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ g ℓ = levelAutBar q M' ζ γ)
    (hCIg_def : ∀ ℓ, CIg ℓ = Cinf.comap (g ℓ))

    (hSI_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : fieldBar q M'), f ∈ SI Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ SI Q)
    (hχ₀I_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : ↥(SI Q)), χ₀I Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), (hSI_inert τ hτ h1 Q hQ (f : fieldBar q M')).mp f.2⟩ = χ₀I Q f) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ ℓ Q, Q ∉ NIg → ∀ P, P ∈ {P | g ℓ • P ∈ discI Q} ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ {P | g ℓ • P ∈ discI Q} := by
  intro τ hτ h1 ℓ Q hQ P
  obtain ⟨-, γ₀, hγ₀, -, hgeq⟩ := hg ℓ
  have hgA := ModularCurve.baseAut_arithmeticGalois_mem_iff (xHFunctionField (q ^ 2 * M') (levelH q M')) A hτ
  have hD : ∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P ∈ discI Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ discI Q := fun P =>
    AlgebraicCurve.SemilinearAut.mem_iff_smul_mem_of_forall_mem_iff_sections (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ) hgA (SI Q) (χ₀I Q)
      (hSI_inert τ hτ h1 Q hQ) (hχ₀I_inert τ hτ h1 Q hQ) (discI Q) ((hstalkI Q hQ).2) P
  simp only [Set.mem_setOf_eq]
  rw [hgeq, ← ofAlgAut_smul_place, ← ofAlgAut_smul_place, hD (SemilinearAut.ofAlgAut (levelAutBar q M' ζ γ₀) • P),
    ← mul_smul, ← mul_smul,
    ModularCurve.FullLevel.arithmeticGalois_mul_ofAlgAut_levelAutBar_of_tameCharacter_eq_one q M' hqM' A hA π hπ hτ h1 ζ γ₀ hγ₀]

end ModularCurve.FullLevel.W1c.Pen
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

end Inlined_MAIN
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing.Idx P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel.W1c.Plumbing"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (CIg : CuspidalType.ProjLine q → ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (Cinf : ComponentChart A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')))
    (RI : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hRI : RI.integers = OIg (lineInfty q))
    (hCinfint : Cinf.integers = RI.integers)
    (hCinfres : ∀ (f : fieldBar q M') (hC : f ∈ Cinf.integers) (hR : f ∈ RI.integers), Cinf.residue ⟨f, hC⟩ = RI.residue ⟨f, hR⟩)
    (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
    (discI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Set (Place (AlgebraicClosure ℚ) (fieldBar q M')))
    (coordI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → (fieldBar q M'))
    (hnodesI : Cinf.nodes = NIg) (hfamI : RI.DiscFamily NIg discI coordI)
    (SI : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → Subring (fieldBar q M'))
    (χ₀I : ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), ↥(SI Q) →+* ResidueField A)
    (hstalkI : (∀ Q, Q ∉ NIg → (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ RI.integers) ∧
        ∀ P, P ∈ discI Q ↔ P.IsRational ∧
          (∀ f : ↥(SI Q), (f : fieldBar q M') ∈ P.toValuationSubring ∧ P.evalAt (f : fieldBar q M') ∈ A) ∧
          (∀ f : ↥(SI Q), A.valuation (P.evalAt (f : fieldBar q M')) < 1 ↔ χ₀I Q f = 0)))
    (hdomI : ∀ P, P ∈ Cinf.dom ↔ ∃ Q, Q ∉ NIg ∧ P ∈ discI Q)
    (hpmI : ∀ P Q, Q ∉ NIg → P ∈ discI Q → Cinf.placeMap P = Q)
    (hpmI_off : ∀ P P', P ∉ Cinf.dom → P' ∉ Cinf.dom → Cinf.placeMap P = Cinf.placeMap P')
    (hNstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), RI.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg)
    (hdiscstabI : ∀ τ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}), ∀ (hτ : ∀ f : (fieldBar q M'), τ f ∈ RI.integers ↔ f ∈ RI.integers)
      (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))), Q ∉ NIg → RegularProlongation.smulDisc τ (discI Q) = discI (RI.resAut τ hτ • Q))
    (g : CuspidalType.ProjLine q → ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')))
    (hg : ∀ ℓ, g ℓ ∈ (Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
          ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}) ∧ ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧ g ℓ = levelAutBar q M' ζ γ)
    (hCIg_def : ∀ ℓ, CIg ℓ = Cinf.comap (g ℓ))

    (hSI_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : fieldBar q M'), f ∈ SI Q ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ SI Q)
    (hχ₀I_inert : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
      (h1 : A.tameCharacter π τ = 1) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hQ : Q ∉ NIg)
      (f : ↥(SI Q)), χ₀I Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : fieldBar q M'), (hSI_inert τ hτ h1 Q hQ (f : fieldBar q M')).mp f.2⟩ = χ₀I Q f) :
    ∀ τ ∈ A.inertiaSubgroupIn ℚ, A.tameCharacter π τ = 1 →
      ∀ ℓ Q, Q ∉ NIg → ∀ P, P ∈ {P | g ℓ • P ∈ discI Q} ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • P ∈ {P | g ℓ • P ∈ discI Q}  :=
  ModularCurve.FullLevel.W1c.Pen.ig_semilinear_leaf_proof q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr π hπ hπP CIg Cinf RI hRI hCinfint hCinfres NIg discI coordI hnodesI hfamI SI χ₀I hstalkI hdomI hpmI hpmI_off hNstabI hdiscstabI g hg hCIg_def hSI_inert hχ₀I_inert

end S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_igusaDiscs_inertia_stable_of_stalkInert_of_eq_two_of_dvd (solution)
