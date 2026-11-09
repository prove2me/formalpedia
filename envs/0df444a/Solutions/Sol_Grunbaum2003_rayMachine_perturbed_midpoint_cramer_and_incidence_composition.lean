-- Prove2me | solution 1 for Grunbaum2003.rayMachine_perturbed_midpoint_cramer_and_incidence_composition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:32:05.302214+00:00
-- url     : https://prove2.me/submissions/94833e76-9e54-4f49-aef6-1a1e1364264e

import Definitions.Def_Grunbaum2003_IsPolytopeRayOracle
import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep
import Definitions.Def_Grunbaum2003_rayMachineRun
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open scoped BigOperators Matrix Classical

open Grunbaum2003

lemma rayMachine_prefix_and_perturbed_query_composition {d : ℕ}
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
    (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
    (hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (pBase uBase epsCell minBase : ℤ) (q : ℕ),
      (fun i : Fin d =>
        source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      let steps := perturbedRayQuerySteps d pBase uBase epsCell
      minBase ≤ outBase ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q + 1 ∧
        (∀ i : Fin d,
          c'.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
        (∀ z : ℤ, z < outBase → c'.tape z = source z))
    (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (hDir_ne : (fun i : Fin d =>
      c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0) :
    let prog := pre ++
      (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
    let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
    minBase ≤ outBase ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries + 1 ∧
      (∀ i : Fin d,
        c.tape (outBase + (i.val : ℤ)) =
          oracle (fun j : Fin d =>
            c_pre.tape (pBase + (j.val : ℤ)) +
              c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
      (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z) := by
  intro prog outBase
  let t_pq := perturbedRayQuerySteps d pBase uBase epsCell
  obtain ⟨hMin, c_pq, hRun_pq, _, hHalt_pq, hHead_pq, hQ_pq, hVal_pq, hPres_pq⟩ :=
    hPerturbedQueryProg oracle c_pre.tape pBase uBase epsCell minBase c_pre.queries hDir_ne
  have hRel := hRelocate pre (perturbedRayQueryProgram d pBase uBase epsCell minBase)
    oracle t_pq ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_pq := hRelocate pre (perturbedRayQueryProgram d pBase uBase epsCell minBase)
    oracle 0 c_pq
  refine ⟨hMin, t_pre + t_pq, relocateCfg pre.length c_pq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_pq, Option.map_some]
  · exact hRel_pq.2.2.2.2.2 hHalt_pq
  · rw [hRel_pq.2.1, hHead_pq]
  · rw [hRel_pq.2.2.2.1, hQ_pq]
  · intro i
    rw [hRel_pq.2.2.1]
    exact hVal_pq i
  · intro z hz
    rw [hRel_pq.2.2.1]
    exact hPres_pq z hz

lemma rayMachine_prefix_and_midpoint_composition {d : ℕ}
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
    let prog := pre ++
      (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
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
  let t_mp := midpointVecSteps d pBase qBase
  obtain ⟨hMin, c_mp, hRun_mp, _, hHalt_mp, hHead_mp, hQ_mp, hVal_mp, hPres_mp⟩ :=
    hMidpointProg oracle c_pre.tape pBase qBase minBase c_pre.queries
  have hRel := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle t_mp ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_mp := hRelocate pre (midpointVecProgram d pBase qBase minBase)
    oracle 0 c_mp
  refine ⟨hMin, t_pre + t_mp, relocateCfg pre.length c_mp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_mp, Option.map_some]
  · exact hRel_mp.2.2.2.2.2 hHalt_mp
  · rw [hRel_mp.2.1, hHead_mp]
  · rw [hRel_mp.2.2.2.1, hQ_mp]
  · intro i
    rw [hRel_mp.2.2.1]
    exact hVal_mp i
  · intro z hz
    rw [hRel_mp.2.2.1]
    exact hPres_mp z hz

lemma rayFrame_cramer_normal_writes_true_facet_row {d m : ℕ}
    {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (S : Finset (Fin m))
    (hFrameCramer2 : ∀ (v : Matrix (Fin d) (Fin d) ℝ), LinearIndependent ℝ v →
      ∀ (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      (∀ i, v i ∈ P) →
      ∀ (p p₀ : Fin d → ℝ), p ∈ frontier P → p = ∑ i, w i • v i →
      (∀ j ∈ S, L j p < 1) →
      (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
      v.det ≠ 0 ∧ ∃ i_new : Fin m,
        i_new ∉ S ∧
        L i_new p₀ = 1 ∧
        ∀ x : Fin d → ℝ,
          ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x)
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
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
    (vBase minBase : ℤ) (q : ℕ)
    (w : Fin d → ℝ) (hw_pos : ∀ i, 0 < w i) (hw_sum : ∑ i, w i = 1)
    (p p₀ : Fin d → ℝ)
    (hLin : LinearIndependent ℝ
      (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))))
    (hv_P : ∀ i : Fin d,
      (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P)
    (hp_front : p ∈ frontier P)
    (hp_eq : p = ∑ i : Fin d,
      w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))))
    (hp_S : ∀ j ∈ S, L j p < 1)
    (hp_p₀ : ∀ k : Fin m, L k p = 1 → L k p₀ = 1) :
    let prog := cramerRowProgram d vBase minBase
    let outBase := cramerRowDest d vBase minBase
    let steps := cramerRowSteps d vBase
    minBase ≤ outBase ∧
    ∃ (c' : RayConfiguration) (i_new : Fin m),
      i_new ∉ S ∧
      L i_new p₀ = 1 ∧
      rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
      c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
      c'.head = 0 ∧ c'.queries = q ∧
      (∀ x : Fin d → ℝ,
        ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
      (∀ z : ℤ, z < outBase → c'.tape z = source z) := by
  intro prog outBase steps
  let v : Matrix (Fin d) (Fin d) ℝ :=
    fun i j => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))
  obtain ⟨hdet, i_new, hi_not_S, hi_p₀, hi_row⟩ :=
    hFrameCramer2 v hLin w hw_pos hw_sum hv_P p p₀ hp_front hp_eq hp_S hp_p₀
  obtain ⟨hMin, c', hRun, hPC, hHalt, hHead, hQ, hVal, hPres⟩ :=
    hCramerProg oracle source vBase minBase q hdet
  refine ⟨hMin, c', i_new, hi_not_S, hi_p₀, hRun, hPC, hHalt, hHead, hQ, ?_, hPres⟩
  intro x
  have hcongr : (∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k) =
      ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hVal k]
  rw [hcongr, hi_row x]

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
  obtain ⟨hMin, c_inc, hRun_inc, _, hHalt_inc, hHead_inc, hQ_inc, hVal_inc, hPres_inc⟩ :=
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
    exact hVal_inc j k
  · intro z hz
    rw [hRel_inc.2.2.1]
    exact hPres_inc z hz

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
       (perturbedRayQueryProgram : ℕ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (perturbedRayQueryDest : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (perturbedRayQuerySteps : ℕ → ℤ → ℤ → ℤ → ℕ)
       (_hPerturbedQueryProg : ∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (pBase uBase epsCell minBase : ℤ) (q : ℕ),
          (fun i : Fin d =>
            source (pBase + (i.val : ℤ)) + source epsCell * source (uBase + (i.val : ℤ))) ≠ 0 →
          let prog := perturbedRayQueryProgram d pBase uBase epsCell minBase
          let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
          let steps := perturbedRayQuerySteps d pBase uBase epsCell
          minBase ≤ outBase ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q + 1 ∧
            (∀ i : Fin d,
              c'.tape (outBase + (i.val : ℤ)) =
                oracle (fun j : Fin d =>
                  source (pBase + (j.val : ℤ)) + source epsCell * source (uBase + (j.val : ℤ))) i) ∧
            (∀ z : ℤ, z < outBase → c'.tape z = source z))
       (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (pBase uBase epsCell minBase : ℤ),
      rayMachineRun (pre ++
          (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      (fun i : Fin d =>
        c_pre.tape (pBase + (i.val : ℤ)) + c_pre.tape epsCell * c_pre.tape (uBase + (i.val : ℤ))) ≠ 0 →
      let prog := pre ++
        (perturbedRayQueryProgram d pBase uBase epsCell minBase).map (relocateInst pre.length)
      let outBase := perturbedRayQueryDest d pBase uBase epsCell minBase
      minBase ≤ outBase ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries + 1 ∧
        (∀ i : Fin d,
          c.tape (outBase + (i.val : ℤ)) =
            oracle (fun j : Fin d =>
              c_pre.tape (pBase + (j.val : ℤ)) +
                c_pre.tape epsCell * c_pre.tape (uBase + (j.val : ℤ))) i) ∧
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
      let prog := pre ++
        (midpointVecProgram d pBase qBase minBase).map (relocateInst pre.length)
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
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)} (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
       (S : Finset (Fin m)),
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
            ∑ k : Fin d, ((v.updateCol k (fun _ => 1)).det / v.det) * x k = L i_new x) →
      ∀ (cramerRowProgram : ℕ → ℤ → ℤ → List RayInstruction)
        (cramerRowDest : ℕ → ℤ → ℤ → ℤ)
        (cramerRowSteps : ℕ → ℤ → ℕ),
      (∀ (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
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
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) →
      ∀ (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (source : ℤ → ℝ)
        (vBase minBase : ℤ) (q : ℕ)
        (w : Fin d → ℝ), (∀ i, 0 < w i) → (∑ i, w i = 1) →
      ∀ (p p₀ : Fin d → ℝ),
        LinearIndependent ℝ
          (fun i j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ i : Fin d,
          (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) ∈ P) →
        p ∈ frontier P →
        p = ∑ i : Fin d,
          w i • (fun j : Fin d => source (vBase + (i.val : ℤ) * (d : ℤ) + (j.val : ℤ))) →
        (∀ j ∈ S, L j p < 1) →
        (∀ k : Fin m, L k p = 1 → L k p₀ = 1) →
        let prog := cramerRowProgram d vBase minBase
        let outBase := cramerRowDest d vBase minBase
        let steps := cramerRowSteps d vBase
        minBase ≤ outBase ∧
        ∃ (c' : RayConfiguration) (i_new : Fin m),
          i_new ∉ S ∧
          L i_new p₀ = 1 ∧
          rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
          c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
          c'.head = 0 ∧ c'.queries = q ∧
          (∀ x : Fin d → ℝ,
            ∑ k : Fin d, c'.tape (outBase + (k.val : ℤ)) * x k = L i_new x) ∧
          (∀ z : ℤ, z < outBase → c'.tape z = source z)) ∧
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
        (∀ z : ℤ, z < outBase → c.tape z = c_pre.tape z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro run_add relocateInst relocateCfg hRelocate perturbedRayQueryProgram perturbedRayQueryDest
      perturbedRayQuerySteps hPerturbedQueryProg pre oracle t_pre c_pre pBase uBase epsCell minBase
      hRun_pre hDir_ne
    exact rayMachine_prefix_and_perturbed_query_composition run_add relocateInst relocateCfg hRelocate
      perturbedRayQueryProgram perturbedRayQueryDest perturbedRayQuerySteps hPerturbedQueryProg
      pre oracle t_pre c_pre pBase uBase epsCell minBase hRun_pre hDir_ne
  · intro run_add relocateInst relocateCfg hRelocate midpointVecProgram midpointVecDest
      midpointVecSteps hMidpointProg pre oracle t_pre c_pre pBase qBase minBase hRun_pre
    exact rayMachine_prefix_and_midpoint_composition run_add relocateInst relocateCfg hRelocate
      midpointVecProgram midpointVecDest midpointVecSteps hMidpointProg
      pre oracle t_pre c_pre pBase qBase minBase hRun_pre
  · intro m P L S hFrameCramer2 cramerRowProgram cramerRowDest cramerRowSteps hCramerProg
      oracle source vBase minBase q w hw_pos hw_sum p p₀ hLin hv_P hp_front hp_eq hp_S hp_p₀
    exact rayFrame_cramer_normal_writes_true_facet_row L S hFrameCramer2 cramerRowProgram
      cramerRowDest cramerRowSteps hCramerProg oracle source vBase minBase q w hw_pos hw_sum
      p p₀ hLin hv_P hp_front hp_eq hp_S hp_p₀
  · intro run_add relocateInst relocateCfg hRelocate facetVertexIncidenceMatrixProgram
      facetVertexIncidenceMatrixDest facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC
      hIncMatrixProg m V pre oracle t_pre c_pre lBase xBase minBase hRun_pre
    exact rayMachine_prefix_and_incidence_matrix_composition run_add relocateInst relocateCfg hRelocate
      facetVertexIncidenceMatrixProgram facetVertexIncidenceMatrixDest
      facetVertexIncidenceMatrixSteps facetVertexIncidenceMatrixPC hIncMatrixProg
      pre oracle t_pre c_pre lBase xBase minBase hRun_pre
