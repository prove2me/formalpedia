-- Prove2me | solution 1 for Grunbaum2003.rayFrame_init_extension_axis_and_step_eps_composition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:50.860247+00:00
-- url     : https://prove2.me/submissions/1901631a-49b9-4be6-bc06-f8e526e43814

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

lemma exists_face_and_exposed_vertex_equiv {d : ℕ} {P : Set (Fin d → ℝ)}
    (hFaces : ∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P))
    (V : Finset (Fin d → ℝ))
    (hV_exp : (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}})
    (hV_card : V.card = faceCount P 0) :
    ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
      (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
      ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V := by
  obtain ⟨n, ⟨e⟩⟩ := hFaces
  let eFin : Fin (faceCount P 0) ≃ V := (Finset.equivFinOfCardEq hV_card).symm
  let eSet : V ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}} := Equiv.setCongr hV_exp
  let vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}} := eFin.trans eSet
  refine ⟨n, e, vEnum, fun k => ?_⟩
  exact (eFin k).property

lemma rayFrame_init_of_uncertified_extremePoint {d m : ℕ} (hd : 2 ≤ d)
    {P : Set (Fin d → ℝ)} (hP : IsDPolytope P) (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (hP_L : P = {x | ∀ i, L i x ≤ 1})
    {oracle : (Fin d → ℝ) → (Fin d → ℝ)} (hOracle : IsPolytopeRayOracle P oracle)
    (S : Finset (Fin m)) {v : Fin d → ℝ}
    (hv : v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ)
    (hne : oracle v ≠ v) :
    let p₀ := oracle v
    let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
    let w₁ : Fin 1 → ℝ := fun _ => 1
    v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
      LinearIndependent ℝ v₁ ∧
      (∀ i : Fin 1, 0 < w₁ i) ∧
      (∑ i : Fin 1, w₁ i = 1) ∧
      p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
      (∀ i : Fin 1, v₁ i ∈ P) ∧
      (∀ j ∈ S, L j p₀ < 1) ∧
      (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1) := by
  intro p₀ v₁ w₁
  have hd_pos : 0 < d := by omega
  have hP_conv : Convex ℝ P := by
    rcases hP.1 with ⟨W, _, _, rfl⟩
    exact convex_convexHull ℝ W
  have hP_closed : IsClosed P := by
    rw [hP_L]
    have h_eq : {x : Fin d → ℝ | ∀ i : Fin m, L i x ≤ 1} =
        ⋂ i : Fin m, {x : Fin d → ℝ | L i x ≤ 1} := by ext x; simp
    rw [h_eq]
    exact isClosed_iInter (fun i => isClosed_le (L i).continuous continuous_const)
  have hPQ : P ⊆ {x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1} := by
    intro x hx i hi; rw [hP_L] at hx; exact hx i
  let eS : Fin S.card ≃ S := (Finset.equivFin S).symm
  let LS : Fin S.card → (Fin d → ℝ) →ₗ[ℝ] ℝ := fun j => (L (eS j).val).toLinearMap
  have hv_LS : ∀ j : Fin S.card, LS j v ≤ 1 := by
    intro j
    exact hv.1 (eS j).val (eS j).property
  have hSector := Grunbaum2003.rayOracle_local_sector_and_known_facet_exclusion.{0}.2.1
    hd_pos hP_conv hP_closed h0 hPQ hOracle hv hne LS hv_LS
  have hv_ne : v ≠ 0 := hSector.1
  have hp₀_front : p₀ ∈ frontier P := (hOracle v hv_ne).1
  have hp₀_P : p₀ ∈ P := by
    rw [hP_closed.frontier_eq] at hp₀_front
    exact hp₀_front.1
  have hp₀_ne : p₀ ≠ 0 := by
    intro hzero
    exact hp₀_front.2 (hzero ▸ h0)
  have hLin : LinearIndependent ℝ v₁ := by
    rw [linearIndependent_unique_iff]
    exact hp₀_ne
  have hp₀_S : ∀ j ∈ S, L j p₀ < 1 := by
    intro j hj
    have hlt := hSector.2 (eS.symm ⟨j, hj⟩)
    simpa [LS, eS] using hlt
  refine ⟨hv_ne, hp₀_ne, hp₀_P, hp₀_front, hLin, ?_, ?_, ?_, ?_, hp₀_S, ?_⟩
  · intro _; norm_num [w₁]
  · simp [w₁]
  · simp [w₁, v₁]
  · intro _; exact hp₀_P
  · intro k hk _; exact hk

lemma rayFrame_exists_extension_axis_and_coord {d r : ℕ}
    {P : Set (Fin d → ℝ)} (h0 : (0 : Fin d → ℝ) ∈ interior P)
    (v : Fin r → Fin d → ℝ) (hLin : LinearIndependent ℝ v) (hr : r < d)
    (w : Fin r → ℝ) (p : Fin d → ℝ) (hp_front : p ∈ frontier P)
    (hp_eq : p = ∑ i : Fin r, w i • v i) :
    ∃ (i_axis j_coord : Fin d),
      Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
      j_coord ≠ i_axis ∧
      p j_coord ≠ 0 := by
  obtain ⟨coordinateAxis, _, _, hAxis, _, _, _, hExtAxis, hCoord, _, _⟩ :=
    Grunbaum2003.rayFrame_boundary_extension_axes_and_cramer_normal
  obtain ⟨i_axis, hi_not_span⟩ := hExtAxis v hLin hr
  have hp_ne : p ≠ 0 := by
    intro hzero
    exact hp_front.2 (hzero ▸ h0)
  have hp_mem : p ∈ Submodule.span ℝ (Set.range v) := by
    rw [hp_eq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨j_coord, hj_ne, hpj_ne⟩ :=
    hCoord (Submodule.span ℝ (Set.range v)) p hp_mem hp_ne i_axis hi_not_span
  rw [hAxis d i_axis] at hi_not_span
  exact ⟨i_axis, j_coord, hi_not_span, hj_ne, hpj_ne⟩

lemma rayMachine_prefix_and_step_eps_composition {d : ℕ}
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
    (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
    (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
    (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
    (hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
      (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
      0 < source aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (pBase + (i.val : ℤ)) < 1) →
      let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let steps := stepEpsSteps d k rowBase pBase uBase aCell
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          source (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ c' : RayConfiguration,
        rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
        c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
        c'.head = 0 ∧ c'.queries = q ∧
        c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
        ∀ z : ℤ, z < dst → c'.tape z = source z)
    {k : ℕ} (pre : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ)
    (hRun_pre : rayMachineRun (pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
      oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
        some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩))
    (ha_pos : 0 < c_pre.tape aCell)
    (hSlack : ∀ j : Fin k,
      ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        c_pre.tape (pBase + (i.val : ℤ)) < 1) :
    let prog := pre ++
      (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
    let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
    let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
      ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
        c_pre.tape (xBase + (i.val : ℤ))
    let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
    let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
    minBase ≤ dst ∧
    ∃ (t : ℕ) (c : RayConfiguration),
      rayMachineRun prog oracle t
        { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
      prog[c.pc]? = some .halt ∧
      c.head = 0 ∧
      c.queries = c_pre.queries ∧
      c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
      (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z) := by
  intro prog dst rowVal δ M
  let t_se := stepEpsSteps d k rowBase pBase uBase aCell
  obtain ⟨hMin, c_se, hRun_se, _, hHalt_se, hHead_se, hQ_se, hVal_se, hPres_se⟩ :=
    @hStepEpsProg k oracle c_pre.tape rowBase pBase uBase aCell minBase c_pre.queries ha_pos hSlack
  have hRel := hRelocate pre (stepEpsProgram d k rowBase pBase uBase aCell minBase)
    oracle t_se ⟨0, 0, c_pre.tape, c_pre.queries⟩
  have hRel_se := hRelocate pre (stepEpsProgram d k rowBase pBase uBase aCell minBase)
    oracle 0 c_se
  refine ⟨hMin, t_pre + t_se, relocateCfg pre.length c_se, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add, hRun_pre, Option.bind_some, hRel.2.2.2.2.1, hRun_se, Option.map_some]
  · exact hRel_se.2.2.2.2.2 hHalt_se
  · rw [hRel_se.2.1, hHead_se]
  · rw [hRel_se.2.2.2.1, hQ_se]
  · rw [hRel_se.2.2.1]
    exact hVal_se
  · intro z hz
    rw [hRel_se.2.2.1]
    exact hPres_se z hz

theorem solution (d : ℕ) (hd : 2 ≤ d) :
    (∀ {P : Set (Fin d → ℝ)},
      (∃ n : ℕ, Nonempty (Fin n ≃ PolytopeFace P)) →
      ∀ (V : Finset (Fin d → ℝ)),
        (V : Set (Fin d → ℝ)) = {x : Fin d → ℝ | IsExposed ℝ P {x}} →
        V.card = faceCount P 0 →
        ∃ (n : ℕ) (_e : Fin n ≃ PolytopeFace P)
          (vEnum : Fin (faceCount P 0) ≃ {x : Fin d → ℝ | IsExposed ℝ P {x}}),
          ∀ k : Fin (faceCount P 0), (vEnum k).val ∈ V) ∧
    (∀ {m : ℕ} {P : Set (Fin d → ℝ)}, IsDPolytope P → (0 : Fin d → ℝ) ∈ interior P →
      ∀ (L : Fin m → (Fin d → ℝ) →L[ℝ] ℝ),
        P = {x | ∀ i, L i x ≤ 1} →
        ∀ {oracle : (Fin d → ℝ) → (Fin d → ℝ)}, IsPolytopeRayOracle P oracle →
          ∀ (S : Finset (Fin m)) {v : Fin d → ℝ},
            v ∈ ({x : Fin d → ℝ | ∀ i ∈ S, L i x ≤ 1}).extremePoints ℝ →
            oracle v ≠ v →
            let p₀ := oracle v
            let v₁ : Fin 1 → Fin d → ℝ := fun _ => p₀
            let w₁ : Fin 1 → ℝ := fun _ => 1
            v ≠ 0 ∧ p₀ ≠ 0 ∧ p₀ ∈ P ∧ p₀ ∈ frontier P ∧
              LinearIndependent ℝ v₁ ∧
              (∀ i : Fin 1, 0 < w₁ i) ∧
              (∑ i : Fin 1, w₁ i = 1) ∧
              p₀ = ∑ i : Fin 1, w₁ i • v₁ i ∧
              (∀ i : Fin 1, v₁ i ∈ P) ∧
              (∀ j ∈ S, L j p₀ < 1) ∧
              (∀ k : Fin m, L k p₀ = 1 → ∀ i : Fin 1, L k (v₁ i) = 1)) ∧
    (∀ {r : ℕ} {P : Set (Fin d → ℝ)}, (0 : Fin d → ℝ) ∈ interior P →
      ∀ (v : Fin r → Fin d → ℝ), LinearIndependent ℝ v → r < d →
        ∀ (w : Fin r → ℝ) (p : Fin d → ℝ),
          p ∈ frontier P → p = ∑ i : Fin r, w i • v i →
          ∃ (i_axis j_coord : Fin d),
            Pi.single i_axis (1 : ℝ) ∉ Submodule.span ℝ (Set.range v) ∧
            j_coord ≠ i_axis ∧
            p j_coord ≠ 0) ∧
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
       (stepEpsProgram : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List RayInstruction)
       (stepEpsDest : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ)
       (stepEpsSteps : ℕ → ℕ → ℤ → ℤ → ℤ → ℤ → ℕ)
       (_hStepEpsProg : ∀ {k : ℕ} (oracle : (Fin d → ℝ) → Fin d → ℝ) (source : ℤ → ℝ)
          (rowBase pBase uBase aCell minBase : ℤ) (q : ℕ),
          0 < source aCell →
          (∀ j : Fin k,
            ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
              source (pBase + (i.val : ℤ)) < 1) →
          let prog := stepEpsProgram d k rowBase pBase uBase aCell minBase
          let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
          let steps := stepEpsSteps d k rowBase pBase uBase aCell
          let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
            ∑ i : Fin d, source (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
              source (xBase + (i.val : ℤ))
          let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
          let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
          minBase ≤ dst ∧
          ∃ c' : RayConfiguration,
            rayMachineRun prog oracle steps ⟨0, 0, source, q⟩ = some c' ∧
            c'.pc = steps ∧ prog[c'.pc]? = some .halt ∧
            c'.head = 0 ∧ c'.queries = q ∧
            c'.tape dst = source aCell * δ / (2 * (1 + source aCell * M + δ)) ∧
            ∀ z : ℤ, z < dst → c'.tape z = source z)
       {k : ℕ} (pre : List RayInstruction)
       (oracle : (Fin d → ℝ) → (Fin d → ℝ))
       (t_pre : ℕ) (c_pre : RayConfiguration) (rowBase pBase uBase aCell minBase : ℤ),
      rayMachineRun (pre ++
          (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length))
        oracle t_pre { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } =
          some (relocateCfg pre.length ⟨0, 0, c_pre.tape, c_pre.queries⟩) →
      0 < c_pre.tape aCell →
      (∀ j : Fin k,
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (pBase + (i.val : ℤ)) < 1) →
      let prog := pre ++
        (stepEpsProgram d k rowBase pBase uBase aCell minBase).map (relocateInst pre.length)
      let dst := stepEpsDest d k rowBase pBase uBase aCell minBase
      let rowVal (j : Fin k) (xBase : ℤ) : ℝ :=
        ∑ i : Fin d, c_pre.tape (rowBase + (j.val : ℤ) * (d : ℤ) + (i.val : ℤ)) *
          c_pre.tape (xBase + (i.val : ℤ))
      let δ : ℝ := ∏ j : Fin k, (1 - rowVal j pBase) / (1 + (1 - rowVal j pBase))
      let M : ℝ := 1 + ∑ j : Fin k, (rowVal j uBase) ^ 2
      minBase ≤ dst ∧
      ∃ (t : ℕ) (c : RayConfiguration),
        rayMachineRun prog oracle t
          { pc := 0, head := 0, tape := fun _ => 0, queries := 0 } = some c ∧
        prog[c.pc]? = some .halt ∧
        c.head = 0 ∧
        c.queries = c_pre.queries ∧
        c.tape dst = c_pre.tape aCell * δ / (2 * (1 + c_pre.tape aCell * M + δ)) ∧
        (∀ z : ℤ, z < dst → c.tape z = c_pre.tape z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hFaces V hV_exp hV_card
    exact exists_face_and_exposed_vertex_equiv hFaces V hV_exp hV_card
  · intro m P hP h0 L hP_L oracle hOracle S v hv hne
    exact rayFrame_init_of_uncertified_extremePoint hd hP h0 L hP_L hOracle S hv hne
  · intro r P h0 v hLin hr w p hp_front hp_eq
    exact rayFrame_exists_extension_axis_and_coord h0 v hLin hr w p hp_front hp_eq
  · intro run_add relocateInst relocateCfg hRelocate stepEpsProgram stepEpsDest stepEpsSteps
      hStepEpsProg k pre oracle t_pre c_pre rowBase pBase uBase aCell minBase hRun_pre ha_pos hSlack
    exact rayMachine_prefix_and_step_eps_composition run_add relocateInst relocateCfg hRelocate
      stepEpsProgram stepEpsDest stepEpsSteps hStepEpsProg pre oracle t_pre c_pre
      rowBase pBase uBase aCell minBase hRun_pre ha_pos hSlack
