-- Prove2me | solution 1 for Grunbaum2003.rayMachine_relocated_discovery_gadgets_and_frame_cramer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:00:59.80278+00:00
-- url     : https://prove2.me/submissions/dab6994f-8f3a-438c-8dec-31381cc77bba

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Theorems.Thm_Grunbaum2003_rayOracle_local_sector_and_known_facet_exclusion
import Theorems.Thm_Grunbaum2003_rayFrame_boundary_extension_axes_and_cramer_normal
import Theorems.Thm_Grunbaum2003_ray_oracle_outer_polytope_invariants_and_phased_trace_bound
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators Matrix Classical

open Grunbaum2003

lemma rayMachine_prefix_and_cramer_row_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
    (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
    (cramerRowSteps : ℕ → ℤ → ℕ)
    (hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (vBase minBase : ℤ) (q : ℕ),
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      v.det ≠ 0 →
      let prog := cramerRowProgram d vBase minBase
      let outBase := cramerRowDest d vBase minBase
      let steps := cramerRowSteps d vBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ k : Fin d,
          c'.tape (outBase + (k.val : ℤ)) =
            (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (hDet : Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0) :
    let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
    let outBase := cramerRowDest d vBase minBase
    let v : Matrix (Fin d) (Fin d) ℝ :=
      fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ k : Fin d,
        c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase v
  let t_cr := cramerRowSteps d vBase
  obtain ⟨hMin, c_cr, hRun_cr, _, hHalt_cr, hHead_cr, hQ_cr, hRow_cr, hPres_cr⟩ :=
    hCramerProg oracle c_pre.tape vBase minBase c_pre.queries hDet
  have hRel := hRelocate pre (cramerRowProgram d vBase minBase)
    oracle t_cr ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_cr := hRelocate pre (cramerRowProgram d vBase minBase) oracle 0 c_cr
  refine ⟨hMin, t_pre + t_cr, relocateCfg pre.length c_cr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_cr, Option.map_some]
  · exact hRel_cr.2.2.2.2.2 hHalt_cr
  · rw [hRel_cr.2.1, hHead_cr]
  · rw [hRel_cr.2.2.2.1, hQ_cr]
  · intro k
    rw [hRel_cr.2.2.1]
    exact hRow_cr k
  · intro z hz
    rw [hRel_cr.2.2.1]
    exact hPres_cr z hz

lemma rayMachine_prefix_and_midpoint_vec_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
    (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
    (hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase qBase minBase : ℤ) (q : ℕ),
      let prog := midpointVecProgram d pBase qBase minBase
      let outBase := midpointVecDest d pBase qBase minBase
      let steps := midpointVecSteps d pBase qBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
    let outBase := midpointVecDest d pBase qBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ i : Fin d,
        c.tape (outBase + (i.val : ℤ)) =
          (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_mid := midpointVecSteps d pBase qBase
  obtain ⟨hMin, c_mid, hRun_mid, _, hHalt_mid, hHead_mid, hQ_mid, hVec_mid, hPres_mid⟩ :=
    hMidpointProg oracle c_pre.tape pBase qBase minBase c_pre.queries
  have hRel := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle t_mid ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_mid := hRelocate pre (midpointVecProgram d pBase qBase minBase) oracle 0 c_mid
  refine ⟨hMin, t_pre + t_mid, relocateCfg pre.length c_mid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_mid, Option.map_some]
  · exact hRel_mid.2.2.2.2.2 hHalt_mid
  · rw [hRel_mid.2.1, hHead_mid]
  · rw [hRel_mid.2.2.2.1, hQ_mid]
  · intro i
    rw [hRel_mid.2.2.1]
    exact hVec_mid i
  · intro z hz
    rw [hRel_mid.2.2.1]
    exact hPres_mid z hz

lemma rayMachine_prefix_and_incidence_matrix_composition {d : ℕ}
    (run_add : ∀ (program : List RayInstruction)
      (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
      rayMachineRun program oracle (a + b) c =
        (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
    (relocateInst : ℕ → RayInstruction → RayInstruction)
    (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
    (hRelocate : ∀ (pre program : List RayInstruction)
      (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
      (relocateCfg pre.length c).pc = pre.length + c.pc ∧
      (relocateCfg pre.length c).head = c.head ∧
      (relocateCfg pre.length c).tape = c.tape ∧
      (relocateCfg pre.length c).queries = c.queries ∧
      rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
          (relocateCfg pre.length c) =
        (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
      (program[c.pc]? = some .halt →
        (pre ++ program.map (relocateInst pre.length))[
          (relocateCfg pre.length c).pc]? = some .halt))
    (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
    (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
    (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
    (hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (lBase xBase minBase : ℤ) (q : ℕ),
      let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
      let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        (∀ (j : Fin m) (k : Fin V),
          c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    {m V : ℕ} (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩)) :
    let prog := pre ++
      (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
    let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      (∀ (j : Fin m) (k : Fin V),
        c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
          if (∑ i : Fin d,
              c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
          then (1 : ℝ) else 0) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_inc := facetVertexIncidenceMatrixSteps d m V lBase xBase
  obtain ⟨hMin, c_inc, hRun_inc, _, hHalt_inc, hHead_inc, hQ_inc, hMat_inc, hPres_inc⟩ :=
    @hIncMatrixProg m V oracle c_pre.tape lBase xBase minBase c_pre.queries
  have hRel := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle t_inc ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_inc := hRelocate pre (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase)
    oracle 0 c_inc
  refine ⟨hMin, t_pre + t_inc, relocateCfg pre.length c_inc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_inc, Option.map_some]
  · exact hRel_inc.2.2.2.2.2 hHalt_inc
  · rw [hRel_inc.2.1, hHead_inc]
  · rw [hRel_inc.2.2.2.1, hQ_inc]
  · intro j k
    rw [hRel_inc.2.2.1]
    exact hMat_inc j k
  · intro z hz
    rw [hRel_inc.2.2.1]
    exact hPres_inc z hz

lemma rayFrame_step_and_cramer_facet_identification {d m : ℕ}
    {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x | ∀ j, L j x ≤ 1}) (S : Finset (Fin m)) :
    (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
      p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      q ∉ Submodule.span ℝ (Set.range v) →
      ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
      let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
      let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
      let p' := (1 / 2 : ℝ) • (p + q)
      LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
        p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
        (∀ j ∈ S, L j p' < 1) ∧
        (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
    (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
      v.det ≠ 0 ∧ ∃ i_new : Fin m,
        i_new ∉ S ∧
        L i_new p₀ = 1 ∧
        ∀ x : Fin d → ℝ,
          ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) := by
  obtain ⟨coordinateAxis, frameCramerCoefficients, frameNormal,
    _, hCramer, hNormal, _, _, _, hStep, hFinal⟩ :=
    Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
  refine ⟨?_, ?_⟩
  · intro n v hLin w hw_pos hw_sum hvP p q hpP hqP hp_eq hpS hq_span j_act hjp hjq
    have hRes := hStep L hP_L v hLin w hw_pos hw_sum hvP p q hpP hqP hp_eq hq_span j_act hjp hjq
    refine ⟨hRes.1, hRes.2.1, hRes.2.2.1, hRes.2.2.2.1, hRes.2.2.2.2.1, hRes.2.2.2.2.2.1, ?_,
      hRes.2.2.2.2.2.2⟩
    intro j hjS
    have hjp_lt : L j p < 1 := hpS j hjS
    have hjq_le : L j q ≤ 1 := by rw [hP_L] at hqP; exact hqP j
    change L j ((1 / 2 : ℝ) • (p + q)) < 1
    rw [map_smul, map_add, smul_eq_mul]
    linarith
  · intro v hLin w hw_pos hw_sum hvP p p₀ hp_front hp_eq hpS hp₀
    obtain ⟨hDet, i_new, hNorm_eq, hi_new_p⟩ :=
      hFinal L hP_L v hLin w hw_pos hw_sum hvP p hp_front hp_eq
    have hi_new_not_S : i_new ∉ S := by
      intro hmem
      have hlt := hpS i_new hmem
      linarith
    refine ⟨hDet, i_new, hi_new_not_S, hp₀ i_new hi_new_p, ?_⟩
    intro x
    have h1 := hNormal d v x
    rw [hNorm_eq] at h1
    rw [h1]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hCramer d v k]

theorem solution (d : ℕ) :
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
       (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
       (cramerRowSteps : ℕ → ℤ → ℕ)
       (_hCramerProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (vBase minBase : ℤ) (q : ℕ),
          let v : Matrix (Fin d) (Fin d) ℝ :=
            fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
          v.det ≠ 0 →
          let prog := cramerRowProgram d vBase minBase
          let outBase := cramerRowDest d vBase minBase
          let steps := cramerRowSteps d vBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ k : Fin d,
              c'.tape (outBase + (k.val : ℤ)) =
                (v.updateCol k (fun _ => 1)).det / v.det) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (vBase minBase : ℤ),
      rayMachineRun (pre ++
          (cramerRowProgram d vBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      Matrix.det (fun i j : Fin d => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ≠ 0 →
      let prog := pre ++ (cramerRowProgram d vBase minBase).map (relocateInst pre.length)
      let outBase := cramerRowDest d vBase minBase
      let v : Matrix (Fin d) (Fin d) ℝ :=
        fun i j => c_pre.tape (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ k : Fin d,
          c.tape (outBase + (k.val : ℤ)) = (v.updateCol k (fun _ => 1)).det / v.det) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (midpointVecProgram : ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (midpointVecDest : ℕ → ℤ → ℤ → ℤ → ℤ)
       (midpointVecSteps : ℕ → ℤ → ℤ → ℕ)
       (_hMidpointProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase qBase minBase : ℤ) (q : ℕ),
          let prog := midpointVecProgram d pBase qBase minBase
          let outBase := midpointVecDest d pBase qBase minBase
          let steps := midpointVecSteps d pBase qBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                (source (pBase + (i.val : ℤ)) + source (qBase + (i.val : ℤ))) / 2) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase qBase minBase : ℤ),
      rayMachineRun (pre ++
          (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++ (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
      let outBase := midpointVecDest d pBase qBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            (c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape (qBase + (i.val : ℤ))) / 2) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ (_run_add : ∀ (program : List RayInstruction)
          (oracle : (Fin d → ℝ) → Fin d → ℝ) (a b : ℕ) (c : RayConfiguration),
          rayMachineRun program oracle (a + b) c =
            (rayMachineRun program oracle a c).bind (rayMachineRun program oracle b))
       (relocateInst : ℕ → RayInstruction → RayInstruction)
       (relocateCfg : ℕ → RayConfiguration → RayConfiguration)
       (_hRelocate : ∀ (pre program : List RayInstruction)
          (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (t : ℕ) (c : RayConfiguration),
          (relocateCfg pre.length c).pc = pre.length + c.pc ∧
          (relocateCfg pre.length c).head = c.head ∧
          (relocateCfg pre.length c).tape = c.tape ∧
          (relocateCfg pre.length c).queries = c.queries ∧
          rayMachineRun (pre ++ program.map (relocateInst pre.length)) oracle t
              (relocateCfg pre.length c) =
            (rayMachineRun program oracle t c).map (relocateCfg pre.length) ∧
          (program[c.pc]? = some .halt →
            (pre ++ program.map (relocateInst pre.length))[
              (relocateCfg pre.length c).pc]? = some .halt))
       (facetVertexIncidenceMatrixProgram : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → List RayInstruction)
       (facetVertexIncidenceMatrixDest : ℕ → ℕ → ℕ → ℤ → ℤ → ℤ → ℤ)
       (facetVertexIncidenceMatrixSteps : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (facetVertexIncidenceMatrixPC : ℕ → ℕ → ℕ → ℤ → ℤ → ℕ)
       (_hIncMatrixProg : ∀ {m V : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (lBase xBase minBase : ℤ) (q : ℕ),
          let prog := facetVertexIncidenceMatrixProgram d m V lBase xBase minBase
          let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
          let steps := facetVertexIncidenceMatrixSteps d m V lBase xBase
          let haltPC := facetVertexIncidenceMatrixPC d m V lBase xBase
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = haltPC ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            (∀ (j : Fin m) (k : Fin V),
              c'.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
                if (∑ i : Fin d,
                    source (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                      source (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
                then (1 : ℝ) else 0) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       {m V : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (lBase xBase minBase : ℤ),
      rayMachineRun (pre ++
          (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      let prog := pre ++
        (facetVertexIncidenceMatrixProgram d m V lBase xBase minBase).map (relocateInst pre.length)
      let outBase := facetVertexIncidenceMatrixDest d m V lBase xBase minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        (∀ (j : Fin m) (k : Fin V),
          c.tape (outBase + (j.val : ℤ) * (V : ℤ) + (k.val : ℤ)) =
            if (∑ i : Fin d,
                c_pre.tape (lBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
                  c_pre.tape (xBase + (k.val : ℤ) * (d : ℤ) + (i.val : ℤ))) = 1
            then (1 : ℝ) else 0) ∧
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
      P = {x | ∀ j, L j x ≤ 1} →
      ∀ (S : Finset (Fin m)),
        (∀ {n : ℕ} (v : Fin n → Fin d → ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin n → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p q : Fin d → ℝ), p ∈ P → q ∈ P →
          p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          q ∉ Submodule.span ℝ (Set.range v) →
          ∀ (j_act : Fin m), L j_act p = 1 → L j_act q = 1 →
          let V : Fin (n + 1) → Fin d → ℝ := Fin.cons q v
          let W : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) (fun i => w i / 2)
          let p' := (1 / 2 : ℝ) • (p + q)
          LinearIndependent ℝ V ∧ (∀ i, 0 < W i) ∧ (∑ i, W i = 1) ∧
            p' = ∑ i, W i • V i ∧ (∀ i, V i ∈ P) ∧ p' ∈ frontier P ∧
            (∀ j ∈ S, L j p' < 1) ∧
            (∀ k : Fin m, L k p' = 1 → ∀ i, L k (V i) = 1)) ∧
        (∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
          ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
          (∀ i, v i ∈ P) →
          ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
          (∀ j ∈ S, L j p < 1) →
          (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
          v.det ≠ 0 ∧ ∃ i_new : Fin m,
            i_new ∉ S ∧
            L i_new p₀ = 1 ∧
            ∀ x : Fin d → ℝ,
              ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)) :=
  ⟨fun run_add relocateInst relocateCfg hRelocate cramerRowProgram cramerRowDest cramerRowSteps
      hCramerProg pre oracle t_pre c_pre vBase minBase hRun_pre hDet =>
     rayMachine_prefix_and_cramer_row_composition run_add relocateInst relocateCfg hRelocate
       cramerRowProgram cramerRowDest cramerRowSteps hCramerProg pre oracle t_pre c_pre vBase minBase
       hRun_pre hDet,
   fun run_add relocateInst relocateCfg hRelocate midpointVecProgram midpointVecDest midpointVecSteps
      hMidpointProg pre oracle t_pre c_pre pBase qBase minBase hRun_pre =>
     rayMachine_prefix_and_midpoint_vec_composition run_add relocateInst relocateCfg hRelocate
       midpointVecProgram midpointVecDest midpointVecSteps hMidpointProg pre oracle t_pre c_pre
       pBase qBase minBase hRun_pre,
   fun run_add relocateInst relocateCfg hRelocate facetVertexIncidenceMatrixProgram
      facetVertexIncidenceMatrixDest facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC
      hIncMatrixProg _ _ pre oracle t_pre c_pre lBase xBase minBase hRun_pre =>
     rayMachine_prefix_and_incidence_matrix_composition run_add relocateInst relocateCfg hRelocate
       facetVertexIncidenceMatrixProgram facetVertexIncidenceMatrixDest
       facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC hIncMatrixProg pre oracle t_pre
       c_pre lBase xBase minBase hRun_pre,
   fun L hP_L S => rayFrame_step_and_cramer_facet_identification L hP_L S⟩
