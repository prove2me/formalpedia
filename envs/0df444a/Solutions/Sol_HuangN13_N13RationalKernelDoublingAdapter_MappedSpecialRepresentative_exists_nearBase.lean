-- Prove2me | solution 1 for HuangN13.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:16.309116+00:00
-- url     : https://prove2.me/submissions/5fa7f236-d27a-4628-b670-81383baeda59

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_HuangN13_N13ConcreteGraphRecovery_exists_diskPair_class_eq
import Theorems.Thm_MazurProof_N13TwoAdicAbelChartData_DiskPair_u_injective

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoAdicAbelChartRecover
noncomputable section
namespace NearBaseMumford
variable (D : NearBaseMumford)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem diskPair_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).diskPair = P := by
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  rw [(ofDiskPair P).diskPair_u]
  rfl
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors
namespace MazurProof.N13TwoAdicAbelChartRecover
noncomputable section
namespace NearBaseMumford
variable (D : NearBaseMumford)
@[simp] theorem centeredPic_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic P := by
  rw [(ofDiskPair P).centeredPic_eq_diskPair_centeredPic,
    diskPair_ofDiskPair]
end NearBaseMumford
end
end MazurProof.N13TwoAdicAbelChartRecover
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace MappedSpecialRepresentative
variable {c : Pic₂}
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
/-- Literal special-ideal reduction recovers a disk pair whose centered
Picard class is the prescribed class `c`.  All normalization and Hensel
lifting are supplied by the existing concrete graph-recovery theorem. -/
theorem exists_nearBase
    (R : MappedSpecialRepresentative c) :
    ∃ E : NearBaseMumford, E.centeredPic = c := by
  obtain ⟨P, hP⟩ :=
    HuangN13.N13ConcreteGraphRecovery.exists_diskPair_class_eq
      R.mumford R.map_contract_eq_special
  refine
    ⟨N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair P, ?_⟩
  rw [
    N13TwoAdicAbelChartRecover.NearBaseMumford.centeredPic_ofDiskPair,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic]
  have hPic :
      N13TwoAdicAbelChartPic.DiskPair.pic P =
        c + basePic :=
    hP.symm.trans R.class_eq
  rw [hPic, basePic]
  abel
end MappedSpecialRepresentative
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end


set_option autoImplicit false
open Polynomial
theorem solution {c : MazurProof.N13RationalKernelDoublingAdapter.Pic₂}
    (R : MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative c) :
    ∃ E : MazurProof.N13RationalKernelDoublingAdapter.NearBaseMumford, E.centeredPic = c := by
  exact MazurProof.N13RationalKernelDoublingAdapter.MappedSpecialRepresentative.exists_nearBase R
