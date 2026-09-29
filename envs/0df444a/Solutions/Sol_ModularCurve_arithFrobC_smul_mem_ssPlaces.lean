-- Prove2me | solution 1 for ModularCurve.arithFrobC_smul_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a1eba9b6-8cdb-5568-b23a-806a0e558849

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithFrobC_smul_mem_ssPlaces

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "isSupersingularPlace_iff ssPlaces mem_ssPlaces_iff jGeomGen jNGeomGen IsCentreOf exists_isCentreOf_of_isRational modularFunctionFieldC ssJSet arithFrobC baseAut_arithFrobC_apply arithFrobC_smul_jq arithFrobC_smul_jqN pow_mem_ssJSet_iff"
p2m_open "ModularCurve"

namespace ArithFrobSsPlacesSol

open AlgebraicCurve

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isRational_smul (g : SemilinearAut K F) {v : Place K F} (hv : v.IsRational) :
    (g • v).IsRational := by
  intro y
  obtain ⟨a, ha⟩ := hv ((SemilinearAut.smulResidueRingEquiv g v).symm y)
  refine ⟨SemilinearAut.baseAut g a, ?_⟩
  rw [← SemilinearAut.smulResidueRingEquiv_algebraMap, ha, RingEquiv.apply_symm_apply]

end Generic

section Centre

variable {K : Type*} [Field K] {N : ℕ} [NeZero N]

theorem isCentreOf_smul (g : SemilinearAut K (modularFunctionFieldC K N))
    (hj : g • jGeomGen K N = jGeomGen K N) (hjN : g • jNGeomGen K N = jNGeomGen K N)
    {c : K × K} {w : Place K (modularFunctionFieldC K N)} (h : IsCentreOf K N c w) :
    IsCentreOf K N (SemilinearAut.baseAut g c.1, SemilinearAut.baseAut g c.2) (g • w) := by
  constructor
  · show 0 < (g • w).ord (jGeomGen K N
      - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.1))
    have e : jGeomGen K N - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.1)
        = g • (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.1) := by
      rw [smul_sub, hj, SemilinearAut.smul_algebraMap]
    rw [e, SemilinearAut.ord_smul]
    exact h.1
  · show 0 < (g • w).ord (jNGeomGen K N
      - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.2))
    have e : jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) (SemilinearAut.baseAut g c.2)
        = g • (jNGeomGen K N - algebraMap K (modularFunctionFieldC K N) c.2) := by
      rw [smul_sub, hjN, SemilinearAut.smul_algebraMap]
    rw [e, SemilinearAut.ord_smul]
    exact h.2

end Centre

end ArithFrobSsPlacesSol

end ModularCurve

end

open AlgebraicCurve _root_.ModularCurve _root_.P2MW.S_ModularCurve_arithFrobC_smul_mem_ssPlaces.ModularCurve ModularCurve.ArithFrobSsPlacesSol in
theorem solution (q N : ℕ) [NeZero N] (K : Type) [Field K] [DecidableEq K] [Fact q.Prime]
    [CharP K q] [PerfectField K] :
    ∀ w ∈ ModularCurve.ssPlaces q N K,
      ModularCurve.arithFrobC q K N • w ∈ ModularCurve.ssPlaces q N K := by
  intro w hw
  obtain ⟨hrat, haff, hss⟩ :=
    (isSupersingularPlace_iff q N K w).mp ((mem_ssPlaces_iff q N K).mp hw)
  have hj : arithFrobC q K N • jGeomGen K N = jGeomGen K N := arithFrobC_smul_jq q K N
  have hjN : arithFrobC q K N • jNGeomGen K N = jNGeomGen K N := arithFrobC_smul_jqN q K N
  have hc' := isCentreOf_smul (arithFrobC q K N) hj hjN (exists_isCentreOf_of_isRational hrat haff)
  refine (mem_ssPlaces_iff q N K).mpr ⟨isRational_smul (arithFrobC q K N) hrat,
    hc'.isAffineGeomPlace, ?_⟩
  rw [hc'.evalAt_jGeomGen]
  show SemilinearAut.baseAut (arithFrobC q K N) (w.evalAt (jGeomGen K N)) ∈ ssJSet q K
  rw [baseAut_arithFrobC_apply]
  exact (ModularCurve.pow_mem_ssJSet_iff q (w.evalAt (jGeomGen K N))).mpr hss

end S_ModularCurve_arithFrobC_smul_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_arithFrobC_smul_mem_ssPlaces (solution)
