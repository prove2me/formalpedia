-- Prove2me | solution 1 for NearLinearRSP.TwoResources.Supplement.bounded_ram_preprocessing
-- status  : ACCEPTED   (prove)
-- author  : @k-variant
-- created : 2026-11-25T09:26:25.531456+00:00
-- url     : https://prove2.me/submissions/02d9fe14-8b26-4a3a-b0b4-70f29166ebf6

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_TableMachine
import Theorems.Thm_NearLinearRSP_TwoResources_Implementation_initialization_and_expectation_correct
import Theorems.Thm_NearLinearRSP_TwoResources_Supplement_ram_clock_table_construction

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem build_table_run {k : ℕ} (A : ClockCall k) (hk : 0 < k) (ε : ℝ) (base map keys params height W P : ℕ)
    (site : Site A base map params (2^height) W) (keyStart : map+3*A.I.graph.n+A.I.graph.edges.length ≤ keys)
    (keyEnd : keys + (incidentVertices A.I).length ≤ params) (hdis : W + 2*2^height ≤ P) (hq : 0 < A.q) (hd : 0 < A.d)
    (s : Store) (h : TableInput A base map keys params (2^height) W P s)
    (blank : ∀ x, base+4 ≤ x → x < extent A base → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput A.I ε) (buildTableCmd k A.d) s t n ∧ TableContext A base map keys params (2^height) W P t ∧
      TableImage A base (constructTable A) t ∧ TableFrame A base keys s t ∧ t.nr 203 = extent A base ∧
      (∀ a, TableOuter k a → GridFixed a → a ≠ 203 → t.nr a = s.nr a) ∧
      n ≤ tableCost k A.d A.q (2^height) (incidentVertices A.I).length A.I.graph.edges.length :=
  NearLinearRSP.TwoResources.Supplement.ram_clock_table_construction A hk ε base map keys params height W P site keyStart keyEnd hdis hq hd s h blank

end NearLinearRSP.TwoResources.Supplement.LayerRAM

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

universe u_1

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

theorem run_final_unique :
  ∀ {input : RAMInput} {c : Cmd} {s t u : Store} {n m : ℕ}
    (h : Run input c s t n) (h' : Run input c s u m),
  t = u :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem run_atoms :
  ∀ (input : RAMInput) (as : List Atom) (s : Store),
  Run input (Cmd.atoms as) s (evalAtoms input as s) as.length :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.1.2.1

@[ext] theorem Store.ext :
  ∀ {s t : Store} (hnr : s.nr = t.nr)
    (hrr : s.rr = t.rr) (hnm : s.nm = t.nm) (hrm : s.rm = t.rm),
  s = t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.1.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Structured

theorem Run.nat_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.natWrites),
  t.nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.1.2.2.2.2

theorem Run.real_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (r : ℕ) (hr : r ∉ c.realWrites),
  t.rr r = s.rr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.1

theorem Run.natMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesNatMemory = false),
  t.nm = s.nm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.1

theorem Run.realMemory_frame :
  ∀ {input : RAMInput} {c : Cmd} {s t : Store} {n : ℕ}
    (h : Run input c s t n) (hw : c.writesRealMemory = false),
  t.rm = s.rm :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.1.1.2.1.1.2.2

end NearLinearRSP.TwoResources.Mission.Structured
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem activeVertices_edge_right :
  ∀ (I : Instance) (u v : ℕ)
    (h : (u,v) ∈ I.graph.edges),
  v ∈ activeVertices I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.1.2.2.2.1.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem treeRun_succ :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (n : ℕ) (S : TreeQueue),
  treeRun I allow w (n + 1) S = treePop I allow w (treeRun I allow w n S) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.1.2.2.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
open scoped NNReal
namespace NearLinearRSP.TwoResources

theorem shortestTree_finite_parent :
  ∀ (I : Instance) (allow : ℕ → ℕ → Bool)
    (w : ℕ → ℕ → ℝ) (v : ℕ) (d : ℝ) (hv : v ≠ I.source)
    (hd : (shortestTree I allow w v).distance = some d),
  ∃ u a, (shortestTree I allow w v).parent = some u ∧
      (shortestTree I allow w u).distance = some a ∧ d = a + w u v ∧
      (u,v) ∈ I.graph.edges ∧ allow u v = true ∧
      (shortestTree I allow w u).rank < (shortestTree I allow w v).rank :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.1.2.2.1.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem activeInsert_run :
  ∀ (input : RAMInput) (s : Store) (hz : s.nr 125 = 0),
  ∃ steps ≤ 8, Run input activeInsert s (activeResult s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.1.2.2.2.2

theorem activeResult_frame_register :
  ∀ (s : Store) (r : ℕ)
    (h143 : r ≠ 143) (h144 : r ≠ 144) (h145 : r ≠ 145) (h146 : r ≠ 146),
  (activeResult s).nr r = s.nr r :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.1.1.1

theorem activeVertices_eq_stableFold :
  ∀ (I : Instance),
  activeVertices I = (I.source :: I.graph.edges.flatMap (fun e => [e.1,e.2])).foldl
      stableInsert [] :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.1.2

theorem ActiveRep.empty :
  ∀ (n base array : ℕ) (s : Store)
    (hb : s.nr 141 = base) (ha : s.nr 142 = array) (hc : s.nr 143 = 0)
    (hsep : base + n ≤ array) (hz : ∀ v < n, s.nm (base + v) = 0),
  ActiveRep n base array [] s :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.1.2.2.2.2.2

theorem ActiveRep.insert :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1),
  ActiveRep n base array (stableInsert xs (s.nr 140)) (activeResult s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.1.1

theorem ActiveRep.length_le :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s),
  xs.length ≤ n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.1.2.2.2

theorem ActiveRep.congr :
  ∀ {n base array : ℕ} {xs : List ℕ} {s t : Store}
    (h : ActiveRep n base array xs s)
    (hb : t.nr 141 = s.nr 141) (ha : t.nr 142 = s.nr 142) (hc : t.nr 143 = s.nr 143)
    (hmap : ∀ v < n, t.nm (base + v) = s.nm (base + v))
    (harray : ∀ k < xs.length, t.nm (array + k) = s.nm (array + k)),
  ActiveRep n base array xs t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).1.2.2.2.2.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem encodeInput_edge_left :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k) = e.1 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.1

theorem encodeInput_edge_right :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).naturals (3+2*k+1) = e.2 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.2.1

theorem encodeInput_length :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k) = (I.length e.1 e.2 : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.1.2.2

theorem encodeInput_cost :
  ∀ (I : Instance) (ε : ℝ) (k : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[k]? = some e),
  (encodeInput I ε).reals (2+2*k+1) = (I.cost e.1 e.2 : ℝ) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.1.1.2.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem AdjacencyChain.frame :
  ∀ {mem mem' : ℕ → ℕ} {links token : ℕ} {es : List ℕ}
    (h : AdjacencyChain mem links token es)
    (hf : ∀ e ∈ es, mem' (links + e) = mem (links + e)),
  AdjacencyChain mem' links token es :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.1.1.2.1.2.2.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem adjacencyScanLoop_run :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2)
    (hend : s.nr 160 + remaining = s.nr 122),
  Run input adjacencyScanLoop s (adjacencyScanResult input remaining s) (11*remaining+1) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.1.2

theorem adjacencyScanCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2),
  Run input adjacencyScanCmd s
      (adjacencyScanResult input (s.nr 122) (adjacencyPrepared s)) (11*s.nr 122+3) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.2.1

theorem outgoingIndices_lt :
  ∀ (I : Instance) (count v e : ℕ)
    (he : e ∈ outgoingIndices I count v),
  e < count :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.1.2.2.2.2

theorem adjacencyScanCmd_correct :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (heads links : ℕ)
    (hm : s.nr 122=I.graph.edges.length) (hone : s.nr 126=1) (htwo : s.nr 127=2)
    (hh : s.nr 163=heads) (hl : s.nr 164=links) (hsep : heads+I.graph.n≤links)
    (hzero : ∀ v<I.graph.n, s.nm (heads+v)=0),
  ∃ out, Run (encodeInput I ε) adjacencyScanCmd s out (11*I.graph.edges.length+3) ∧
      AdjacencyPrefix I I.graph.edges.length heads links out.nm ∧
      out.rr=s.rr ∧ out.rm=s.rm ∧
      (∀ a, (a<heads ∨ heads+I.graph.n≤a) →
        (a<links ∨ links+I.graph.edges.length≤a) → out.nm a=s.nm a) ∧
      (∀ r, r≠160 → r≠161 → r≠162 → r≠165 → r≠166 → r≠167 → r≠168 → out.nr r=s.nr r) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.1.2.1.2.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources

theorem firstPositiveLength_le_largestLength :
  ∀ (I : Instance)
    (h : positiveLengths I ≠ []),
  firstPositiveLength I ≤ largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.2.1

theorem largestLength_pos :
  ∀ (I : Instance) (h : positiveLengths I ≠ []),
  0 < largestLength I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.1.2.2

theorem one_le_aspectRatio :
  ∀ (I : Instance),
  1 ≤ aspectRatio I :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.1.1.2.2.2.1.1

end NearLinearRSP.TwoResources
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.NatToReal
open Structured

theorem convertCmd_run :
  ∀ (input : RAMInput) (s : Store),
  ∃ (t : Store) (steps : ℕ), Run input convertCmd s t steps ∧
      t.rr 60 = (s.nr 60 : ℝ) ∧
      steps ≤ 14 * (Nat.log 2 (s.nr 60) + 1) ^ 2 + 5 ∧ Frame s t :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.1.2.1

end NearLinearRSP.TwoResources.Mission.NatToReal
end

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Scan

theorem addSample_summarize :
  ∀ (xs : List (ℝ × ℝ)) (x : ℝ × ℝ),
  addSample (summarize xs) x = summarize (xs++[x]) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.1.1

theorem summarize_edgeSamples :
  ∀ (I : Instance),
  (summarize (edgeSamples I)).found = !(positiveLengths I).isEmpty ∧
    (summarize (edgeSamples I)).minimum = firstPositiveLength I ∧
    (summarize (edgeSamples I)).maximum = largestLength I ∧
    (summarize (edgeSamples I)).sumLength =
      (I.graph.edges.map (fun e => (I.length e.1 e.2 : ℝ))).sum ∧
    (summarize (edgeSamples I)).sumCost =
      (I.graph.edges.map (fun e => (I.cost e.1 e.2 : ℝ))).sum :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.1.2

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Scan
open Structured

theorem maxCmd_run :
  ∀ (input : RAMInput) (s : Store) (dst src : ℕ),
  ∃ n ≤ 3, Run input (maxCmd dst src) s (maxResult s dst src) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.1.2.2.2.2.2

theorem positiveCmd_run :
  ∀ (input : RAMInput) (s : Store)
    (hz : s.nr 153 = 0) (hrz : s.rr 156 = 0),
  ∃ n ≤ 6, Run input positiveCmd s (positiveResult input s) n :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.1.2.2.2.1.1.1.1

end NearLinearRSP.TwoResources.Mission.Scan
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem activeScan_run :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (hz : s.nr 125 = 0) (hone : s.nr 126 = 1)
    (hend : s.nr 147 + remaining = s.nr 148),
  ∃ steps ≤ 12 * remaining + 1,
      Run input activeScan s (activeScanResult input remaining s) steps :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.1.2.2.2.1

theorem activeScan_rep :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n),
  ActiveRep n base array
      ((scannedVertices input (s.nr 147) remaining).foldl stableInsert xs)
      (activeScanResult input remaining s) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.1.2.1

theorem encoded_scannedVertices :
  ∀ (I : Instance) (ε : ℝ),
  scannedVertices (encodeInput I ε) 3 (2 * I.graph.edges.length) =
      I.graph.edges.flatMap (fun e => [e.1,e.2]) :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.1.2.1

theorem ActiveRep.insert_memory_frame :
  ∀ {n base array : ℕ} {xs : List ℕ} {s : Store}
    (h : ActiveRep n base array xs s) (hv : s.nr 140 < n) (hone : s.nr 126 = 1)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeResult s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.1.2.1

theorem activeScan_memory_frame :
  ∀ (input : RAMInput) (remaining : ℕ) (s : Store)
    (n base array : ℕ) (xs : List ℕ) (h : ActiveRep n base array xs s)
    (hone : s.nr 126 = 1)
    (hv : ∀ v ∈ scannedVertices input (s.nr 147) remaining, v < n)
    (a : ℕ) (hb : a < base ∨ base + n ≤ a) (ha : a < array ∨ array + n ≤ a),
  (activeScanResult input remaining s).nm a = s.nm a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.1.2.2.2.1.2.2

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.Queue
open Structured

theorem chooseCapacity_exact :
  ∀ (input : RAMInput) (s : Store),
  ∃ out k, Run input chooseCapacity s out k ∧ k ≤ 3 * Nat.clog 2 (s.nr 10) + 2 ∧
      out.nr 11 = 2 ^ Nat.clog 2 (s.nr 10) ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ out.rr = s.rr ∧
      ∀ a, a ≠ 11 → out.nr a = s.nr a :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.1.1

end NearLinearRSP.TwoResources.Mission.Queue
end

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem setupCmd_run :
  ∀ (I : Instance) (ε : ℝ) (hε : 0<ε) (hε1 : ε<1),
  ∃ out steps, Run (encodeInput I ε) setupCmd initialStore out steps ∧ SetupReady I ε out ∧
      steps≤18*outerQ ε+14*(Nat.log 2 I.graph.n+1)^2+55*I.graph.edges.length+
        8*(outerInputs I ε).length+3*Nat.clog 2 (activeVertices I).length+182 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.1.1.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
namespace NearLinearRSP.TwoResources.Mission.TargetRecords
open Structured

theorem LabelRep.finite_iff :
  ∀ {d : Option ℝ} {sentinel value : ℝ}
    (h : LabelRep d sentinel value),
  value < sentinel ↔ d.isSome = true :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.1.2.2.1.1.2.2.2

end NearLinearRSP.TwoResources.Mission.TargetRecords
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false
section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace NearLinearRSP.TwoResources.Mission.Preprocess
open Structured

theorem zeroTrees_ready :
  ∀ (I : Instance) (ε : ℝ) (s : Store) (hSetup : SetupReady I ε s),
  ∃ out steps, Run (encodeInput I ε) zeroTreesCmd s out steps ∧
      RuntimeReady I ε out ∧ OutputParents I out ∧ TargetRecords.SeedWorld I out ∧
      FutureZero I ε 0 out ∧
      (∀ v < I.graph.n,out.nm (targetAddress v)=0) ∧ out.nr 11=queueCapacity I ∧
      steps ≤ 2*(15*queueCapacity I+
        (38*Nat.clog 2 (2*queueCapacity I)+58)*(activeVertices I).length+
        (19*Nat.clog 2 (2*queueCapacity I)+46)*I.graph.edges.length+7)+6 :=
  (NearLinearRSP.TwoResources.Implementation.initialization_and_expectation_correct.{0}).2.2.2.2.1.1.2.2.1.1

end NearLinearRSP.TwoResources.Mission.Preprocess
end

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem ticks_pos (k : ℕ) (δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    0 < ticks k δ := by
  unfold ticks
  apply Nat.ceil_pos.mpr
  positivity

theorem clockCoordinates_length_le {k : ℕ} (I : MultiInstance k) :
    (clockCoordinates I).length ≤ k := by
  simpa [clockCoordinates] using
    List.length_filter_le (fun r : Fin k => r.val = 0 ∨ 0 < coordinateBudget I 1 r)
      (List.finRange k)

theorem clockCoordinates_mem {k : ℕ} (I : MultiInstance k) (r : Fin k) :
    r ∈ clockCoordinates I ↔ r.val = 0 ∨ 0 < coordinateBudget I 1 r := by
  simp [clockCoordinates]

theorem clockCoordinates_nodup {k : ℕ} (I : MultiInstance k) :
    (clockCoordinates I).Nodup := by
  exact (List.nodup_finRange k).filter _

theorem clockCoordinates_pos {k : ℕ} (I : MultiInstance k) (hk : 0 < k) :
    0 < (clockCoordinates I).length := by
  have hm : (⟨0, hk⟩ : Fin k) ∈ clockCoordinates I :=
    (clockCoordinates_mem I _).mpr (Or.inl rfl)
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)

theorem vectorIndex_cons {d : ℕ} (q a : ℕ) (i : Fin d → ℕ) :
    vectorIndex q (Fin.cons a i) = a * q ^ d + vectorIndex q i := by
  unfold vectorIndex
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel,
    Fin.cons_succ, Fin.val_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  omega

theorem vectorIndex_lt {d q : ℕ} (i : Fin d → ℕ) (hi : ∀ r, i r < q) :
    vectorIndex q i < q ^ d := by
  induction d with
  | zero => simp [vectorIndex]
  | succ d ih =>
    have ht := ih (Fin.tail i) (fun r => hi r.succ)
    have h0 := hi 0
    conv_lhs => rw [← Fin.cons_self_tail i]
    rw [vectorIndex_cons, pow_succ]
    have hmul := Nat.mul_le_mul_right (q ^ d) (Nat.succ_le_of_lt h0)
    nlinarith

theorem put_other {d : ℕ} (T : MultiTable d) (v w : ℕ) (i j : Fin d → ℕ)
    (c : MultiCell) (h : w ≠ v ∨ j ≠ i) : put T v i c w j = T w j := by
  simp only [put]
  exact if_neg (by tauto)

theorem value_of_valid {k : ℕ} (A : ClockCall k) (T : MultiTable A.d)
    (v : ℕ) (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) :
    value A T v i = (T v i).value := by
  simp only [value]
  exact if_neg (by simpa using hi)

theorem selectMin_fold_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) :
    xs.foldl (fun x y => if f y < f x then y else x) a ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · have hm := ih x
      simp only [List.mem_cons] at hm ⊢
      tauto
    · have hm := ih a
      simp only [List.mem_cons] at hm ⊢
      tauto

theorem selectMin_mem {α : Type} (f : α → ℝ) (xs : List α) (a : α) (h : xs ≠ []) :
    selectMin f xs a ∈ xs := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons x xs =>
    simpa [selectMin, List.foldl_cons] using selectMin_fold_mem f xs x

theorem incident_source_mem {k : ℕ} (I : MultiInstance k) :
    I.source ∈ incidentVertices I := by simp [incidentVertices]

theorem incident_valid {k : ℕ} (I : MultiInstance k) (v : ℕ)
    (hv : v ∈ incidentVertices I) : v < I.graph.n := by
  simp only [incidentVertices, List.mem_eraseDups, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact I.source_valid
  · obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
    have hb := I.graph.endpoints e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hb.1
    · exact hb.2

theorem incident_length_bound {k : ℕ} (I : MultiInstance k) :
    (incidentVertices I).length ≤ 1 + 2 * I.graph.edges.length := by
  have hn : (incidentVertices I).Nodup := activeVertices_nodup (lengthInstance I)
  have hsub : incidentVertices I ⊆ I.source :: I.graph.edges.flatMap (fun e => [e.1, e.2]) := by
    intro v hv
    simpa only [incidentVertices, List.mem_eraseDups] using hv
  have h := hn.length_le_of_subset hsub
  simpa [incidentVertices, List.length_flatMap, Nat.mul_comm, Nat.add_comm] using h

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement

theorem fold_preserves {α β : Type*} (f : β → α → β) (P : β → Prop)
    (xs : List α) (b : β) (hb : P b)
    (hf : ∀ a ∈ xs, ∀ b, P b → P (f b a)) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    apply ih (f b a) (hf a (by simp) b hb)
    intro c hc U hU
    exact hf c (by simp [hc]) U hU

noncomputable def settle {d : ℕ} (S : MultiLayer d) (u : ℕ) (i : Fin d → ℕ) : MultiLayer d :=
  { S with
    table := put S.table u i ⟨S.keys u, S.parents u, S.nextRank⟩
    queue := S.queue.erase u
    nextRank := S.nextRank + 1 }

noncomputable def relaxAll {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (u : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (callEdges A).foldl (relax A i u) S

noncomputable def picked {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) : ℕ :=
  selectMin S.keys S.queue A.I.source

noncomputable def runQueue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : MultiLayer A.d :=
  (List.range n).foldl (fun S _ => pop A i S) S

theorem runQueue_succ {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : runQueue A i (n + 1) S = pop A i (runQueue A i n S) := by
  simp [runQueue, List.range_succ, List.foldl_append]

theorem relax_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).table = S.table := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relax_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) (e : ℕ × ℕ) : (relax A i u S e).queue = S.queue := by
  unfold relax
  dsimp only
  split_ifs <;> rfl

theorem relaxAll_table {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).table = S.table := by
  apply fold_preserves (relax A i u) (fun U => U.table = S.table) _ S rfl
  intro e he U hU
  exact (relax_table A i u U e).trans hU

theorem relaxAll_queue {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ) (u : ℕ)
    (S : MultiLayer A.d) : (relaxAll A i u S).queue = S.queue := by
  apply fold_preserves (relax A i u) (fun U => U.queue = S.queue) _ S rfl
  intro e he U hU
  exact (relax_queue A i u U e).trans hU

theorem picked_mem {k : ℕ} (A : ClockCall k) (S : MultiLayer A.d) (h : S.queue ≠ []) :
    picked A S ∈ S.queue := selectMin_mem _ _ _ h

theorem pop_of_nonempty {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (h : S.queue ≠ []) :
    pop A i S = relaxAll A i (picked A S) (settle S (picked A S) i) := by
  unfold pop
  cases he : S.queue with
  | nil => exact (h he).elim
  | cons v vs => simp [relaxAll, settle, picked, selectMin, he]

theorem pop_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) : (pop A i S).queue.Sublist S.queue := by
  by_cases h : S.queue = []
  · simp [pop, h]
  · rw [pop_of_nonempty A i S h, relaxAll_queue]
    exact List.erase_sublist

theorem runQueue_queue_sublist {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) : (runQueue A i n S).queue.Sublist S.queue := by
  induction n with
  | zero => exact List.Sublist.refl _
  | succ n ih => rw [runQueue_succ]; exact (pop_queue_sublist A i _).trans ih

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def marked (s : Store) (r : ℕ) : Store := {s with nr := Function.update s.nr 69 r}

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def added (dst src n : ℕ) (s : Store) : Store :=
  {s with nr := Function.update s.nr dst (s.nr dst + n * s.nr src)}

theorem add_copies_run (input : RAMInput) (dst src : ℕ) (h : src ≠ dst) (n : ℕ) (s : Store) :
    Run input (addCopies dst src n) s (added dst src n s) n := by
  induction n with
  | zero => simpa [addCopies, added] using Run.skip (input := input) s
  | succ n ih =>
    let a : Atom := ⟨.natOp .add dst dst src, trivial⟩
    have he : a.eval input (added dst src n s) = added dst src (n + 1) s := by
      simp [a, added, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, Function.update_of_ne h,
        Function.update_idem, Nat.succ_mul, Nat.add_assoc]
    exact Run.seq ih (he ▸ Run.atom a _)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def partialProduct (s : Store) (j : ℕ) : Store :=
  {s with nr := Function.update (Function.update s.nr 62 (j * s.nr 58)) 61 j}

theorem product_step (input : RAMInput) (s : Store) (j : ℕ) (hone : s.nr 31 = 1) :
    Run input (.atoms productBody) (partialProduct s j) (partialProduct s (j + 1)) 2 := by
  have he : evalAtoms input productBody (partialProduct s j) = partialProduct s (j + 1) := by
    apply Store.ext
    · funext r
      by_cases h61 : r = 61 <;> by_cases h62 : r = 62 <;>
        simp [productBody, partialProduct, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at,
          evalNat, h61, h62, hone, Nat.succ_mul]
    · rfl
    · rfl
    · rfl
  exact he ▸ run_atoms input productBody (partialProduct s j)

theorem product_loop_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1)
    (remaining j : ℕ) (hend : j + remaining = s.nr 57) :
    Run input productLoop (partialProduct s j) (partialProduct s (s.nr 57)) (4 * remaining + 1) := by
  induction remaining generalizing j with
  | zero =>
    have he : j = s.nr 57 := by omega
    subst j
    exact Run.loopFalse (by simp [Guard.eval, natTest, partialProduct])
  | succ n ih =>
    have hg : (Guard.nat .lt 61 57).eval (partialProduct s j) = true := by
      simp [Guard.eval, natTest, partialProduct, show j < s.nr 57 by omega]
    have ht := ih (j + 1) (by omega)
    have hx := Run.loopTrue hg (product_step input s j hone) ht
    simpa only [productLoop, show 1 + 2 + 1 + (4 * n + 1) = 4 * (n + 1) + 1 by omega] using hx

def productResult (s : Store) : Store :=
  let p := partialProduct s (s.nr 57)
  {p with nr := Function.update p.nr 58 (s.nr 57 * s.nr 58)}

theorem product_run (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) :
    Run input productCmd s (productResult s) (4 * s.nr 57 + 4) := by
  have h0 : evalAtoms input productInit s = partialProduct s 0 := by
    simp [evalAtoms, productInit, Atom.eval, Store.ofRAM, ramStep, Store.at, partialProduct]
  have hf : productLast.eval input (partialProduct s (s.nr 57)) = productResult s := by
    simp [productResult, partialProduct, productLast, Atom.eval, Store.ofRAM, ramStep, Store.at]
  have he := Run.seq (h0 ▸ run_atoms input productInit s)
    (Run.seq (product_loop_run input s hone (s.nr 57) 0 (by omega)) (hf ▸ Run.atom productLast _))
  simpa only [productInit, List.length_cons, List.length_nil, productCmd,
    show 2 + (4 * s.nr 57 + 1 + 1) = 4 * s.nr 57 + 4 by omega] using he

def recorded (s : Store) (r : ℕ) : Store := {s with nr := Function.update s.nr (strideReg r) (s.nr 58)}

theorem stride_large (r : ℕ) : 100 ≤ strideReg r := by unfold strideReg CandidateRAM.current; omega
theorem stride_inj {i j : ℕ} : strideReg i = strideReg j ↔ i = j := by
  unfold strideReg CandidateRAM.current; omega

theorem record_run (input : RAMInput) (s : Store) (r : ℕ) (hone : s.nr 31 = 1) :
    let t := productResult (recorded s r)
    Run input (recordCmd r) s t (4 * s.nr 57 + 5) ∧ t.nr 58 = s.nr 57 * s.nr 58 ∧
      t.nr (strideReg r) = s.nr 58 ∧
      (∀ j, j ≠ strideReg r → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := recorded s r
  have hh := stride_large r
  have h31 : 31 ≠ strideReg r := by omega
  have h57 : 57 ≠ strideReg r := by omega
  have h58 : 58 ≠ strideReg r := by omega
  have hp : Run input (.atom (recordStride r)) s p 1 := Run.atom _ _
  have ht := product_run input p (by simpa [p, recorded, Function.update_of_ne h31] using hone)
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have he : 1 + (4 * p.nr 57 + 4) = 4 * s.nr 57 + 5 := by
      simp [p, recorded, Function.update_of_ne h57]; omega
    exact he ▸ Run.seq hp ht
  · simp [productResult, recorded, Function.update_of_ne h57, Function.update_of_ne h58]
  · simp [productResult, recorded, partialProduct, Function.update_of_ne h58.symm,
      Function.update_of_ne (show strideReg r ≠ 61 by omega),
      Function.update_of_ne (show strideReg r ≠ 62 by omega)]
  · intro j hs h₈ h₁ h₂
    simp [productResult, recorded, partialProduct, Function.update_of_ne hs,
      Function.update_of_ne h₈, Function.update_of_ne h₁, Function.update_of_ne h₂]

theorem powers_run (input : RAMInput) (s : Store) (d : ℕ) (hone : s.nr 31 = 1) :
    ∃ t, Run input (powers d) s t (d * (4 * s.nr 57 + 5)) ∧
      t.nr 58 = s.nr 58 * s.nr 57 ^ d ∧
      (∀ r < d, t.nr (strideReg r) = s.nr 58 * s.nr 57 ^ (d - 1 - r)) ∧
      (∀ j, (∀ r < d, j ≠ strideReg r) → j ≠ 58 → j ≠ 61 → j ≠ 62 → t.nr j = s.nr j) ∧
      t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  induction d generalizing s with
  | zero =>
    refine ⟨s, by simpa [powers] using Run.skip (input := input) s, by simp,
      by simp, fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ d ih =>
    let p := productResult (recorded s d)
    obtain ⟨hrun, hp, hs, hf, hrr, hnm, hrm⟩ := record_run input s d hone
    have hg := stride_large d
    have h31 : p.nr 31 = s.nr 31 := hf 31 (by omega) (by decide) (by decide) (by decide)
    have h57 : p.nr 57 = s.nr 57 := hf 57 (by omega) (by decide) (by decide) (by decide)
    obtain ⟨t, ht, htval, hslots, hrest, tr, tn, tm⟩ := ih p (h31.trans hone)
    rw [h57] at ht htval hslots
    have hpc : p.nr 58 = s.nr 57 * s.nr 58 := hp
    rw [hpc] at htval hslots
    refine ⟨t, ?_, ?_, ?_, ?_, tr.trans hrr, tn.trans hnm, tm.trans hrm⟩
    · have hc : 4 * s.nr 57 + 5 + d * (4 * s.nr 57 + 5) = (d + 1) * (4 * s.nr 57 + 5) := by ring
      exact hc ▸ Run.seq hrun ht
    · rw [htval, pow_succ]; ring
    · intro r hr
      by_cases he : r = d
      · subst r
        have hh := hrest (strideReg d) (fun j hj h => by have := stride_inj.mp h; omega)
          (by omega) (by omega) (by omega)
        simpa using hh.trans hs
      · have hj : r < d := by omega
        have hn : d + 1 - 1 - r = (d - 1 - r) + 1 := by omega
        rw [hn, pow_succ, hslots r hj]
        ring
    · intro j hne h₈ h₁ h₂
      exact (hrest j (fun r hr => hne r (by omega)) h₈ h₁ h₂).trans
        (hf j (hne d (by omega)) h₈ h₁ h₂)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependResult)

theorem scanAddress_inside {k : ℕ} (A : ClockCall k) (base v : ℕ) (hv : v < A.I.graph.n)
    (i : Fin A.d → ℕ) (hi : ∀ r, i r < A.q) (x : ℕ) (hx : x < A.d + 4) :
    scanAddress base A.I.graph.n A.q v i + x < extent A base := by
  have hr := vectorIndex_lt i hi
  have hm := Nat.mul_le_mul_right A.I.graph.n (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at hm
  have hrow : vectorIndex A.q i * A.I.graph.n + v + 1 ≤ A.q ^ A.d * A.I.graph.n := by omega
  have hn := Nat.mul_le_mul_left (A.d + 4) hrow
  rw [Nat.mul_add, Nat.mul_one] at hn
  unfold scanAddress extent
  have he : (A.d + 4) * A.I.graph.n * A.q ^ A.d = (A.d + 4) * (A.q ^ A.d * A.I.graph.n) := by ring
  rw [he]; omega

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.AdjacencyRAM
open Mission.Structured Mission.Preprocess

def shift (s : Store) : Store :=
  {s with nr := Function.update s.nr 162 (s.nr 162 + 1)}

def setupOps : List Atom := [⟨.natConst 160 0, trivial⟩, ⟨.natConst 162 4, trivial⟩]
def scanCmd : Cmd := .seq (.atoms setupOps) adjacencyScanLoop

theorem endpoint_shift {k : ℕ} (I : MultiInstance k) (ε : ℝ) (p : ℕ) (hp : 3 ≤ p) :
    (multiInput I ε).naturals (p + 1) = (encodeInput (lengthInstance I) ε).naturals p := by
  have he : p + 1 - 4 = p - 3 := by omega
  simp [multiInput, encodeInput, lengthInstance, he, show p ≠ 0 by omega, show p ≠ 1 by omega,
    show p ≠ 2 by omega, show p + 1 ≠ 2 by omega,
    show p + 1 ≠ 3 by omega]

theorem step_shift {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (hp : 3 ≤ s.nr 162) :
    adjacencyStep (multiInput I ε) (shift s) =
      shift (adjacencyStep (encodeInput (lengthInstance I) ε) s) := by
  have he := endpoint_shift I ε (s.nr 162) hp
  apply Store.ext
  · funext j
    by_cases hj : j = 162
    · subst j
      simp [shift, adjacencyStep, adjacencyLoaded, adjacencyResult, he]
    · simp [shift, adjacencyStep, adjacencyLoaded, adjacencyResult, he, Function.update_apply, hj]
  · rfl
  · simp [shift, adjacencyStep, adjacencyLoaded, adjacencyResult, he]
  · rfl

theorem result_shift {k : ℕ} (I : MultiInstance k) (ε : ℝ) (count : ℕ)
    (s : Store) (hp : 3 ≤ s.nr 162) :
    adjacencyScanResult (multiInput I ε) count (shift s) =
      shift (adjacencyScanResult (encodeInput (lengthInstance I) ε) count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [adjacencyScanResult, step_shift I ε s hp]
    apply ih
    simp [adjacencyStep]
    omega

theorem setup_run (input : RAMInput) (s : Store) :
    Run input (.atoms setupOps) s (shift (adjacencyPrepared s)) 2 := by
  have he : evalAtoms input setupOps s = shift (adjacencyPrepared s) := by
    simp [setupOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
      shift, adjacencyPrepared, Function.update_idem]
  exact he ▸ run_atoms input setupOps s

theorem scan_correct {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (heads links : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hone : s.nr 126 = 1) (htwo : s.nr 127 = 2)
    (hh : s.nr 163 = heads) (hl : s.nr 164 = links) (hsep : heads + I.graph.n ≤ links)
    (hz : ∀ v < I.graph.n, s.nm (heads + v) = 0) :
    ∃ out, Run (multiInput I ε) scanCmd s out (11 * I.graph.edges.length + 3) ∧
      AdjacencyPrefix (lengthInstance I) I.graph.edges.length heads links out.nm ∧
      out.rr = s.rr ∧ out.rm = s.rm ∧
      (∀ a, (a < heads ∨ heads + I.graph.n ≤ a) → (a < links ∨ links + I.graph.edges.length ≤ a) →
        out.nm a = s.nm a) ∧
      (∀ r, r ≠ 160 → r ≠ 161 → r ≠ 162 → r ≠ 165 → r ≠ 166 → r ≠ 167 → r ≠ 168 → out.nr r = s.nr r) := by
  let p := adjacencyPrepared s
  let t := adjacencyScanResult (encodeInput (lengthInstance I) ε) I.graph.edges.length p
  have hp : 3 ≤ p.nr 162 := by simp [p, adjacencyPrepared]
  have htransport := result_shift I ε I.graph.edges.length p hp
  have hr := adjacencyScanLoop_run (multiInput I ε) I.graph.edges.length (shift p)
    (by simp [shift, p, adjacencyPrepared, hone]) (by simp [shift, p, adjacencyPrepared, htwo])
    (by simp [shift, p, adjacencyPrepared, hm])
  have hnew : Run (multiInput I ε) scanCmd s (shift t) (11 * I.graph.edges.length + 3) := by
    rw [htransport] at hr
    simpa only [scanCmd, show 2 + (11 * I.graph.edges.length + 1) = 11 * I.graph.edges.length + 3 by omega]
      using Run.seq (setup_run (multiInput I ε) s) hr
  obtain ⟨out, hrun, henc, hrr, hrm, hnm, hnr⟩ :=
    adjacencyScanCmd_correct (lengthInstance I) ε s heads links hm hone htwo hh hl hsep hz
  have hold := adjacencyScanCmd_run (encodeInput (lengthInstance I) ε) s hone htwo
  rw [hm] at hold
  have he : out = t := Mission.Queue.run_final_unique hrun hold
  subst out
  exact ⟨shift t, hnew, henc, hrr, hrm, hnm, fun r h₀ h₁ h₂ h₅ h₆ h₇ h₈ =>
    (Function.update_of_ne h₂ _ _).trans (hnr r h₀ h₁ h₂ h₅ h₆ h₇ h₈)⟩

end NearLinearRSP.TwoResources.Supplement.AdjacencyRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.IncidentRAM
open Mission.Structured Mission.Preprocess

def ops : List Atom :=
  [ ⟨.natConst 143 0, trivial⟩, ⟨.natCopy 140 123, trivial⟩, ⟨.natConst 147 4, trivial⟩,
    ⟨.natOp .add 148 122 122, trivial⟩, ⟨.natOp .add 148 148 147, trivial⟩ ]

def prepared (s : Store) : Store :=
  {s with nr := Function.update (Function.update (Function.update (Function.update s.nr
    143 0) 140 (s.nr 123)) 147 4) 148 (2 * s.nr 122 + 4)}

def cmd : Cmd := .seq (.atoms ops) (.seq activeInsert activeScan)

def result (input : RAMInput) (s : Store) : Store :=
  activeScanResult input (2 * s.nr 122) (activeResult (prepared s))

theorem vertices_shift {k : ℕ} (I : MultiInstance k) (ε : ℝ) (n p : ℕ) (hp : 3 ≤ p) :
    scannedVertices (multiInput I ε) (p + 1) n = scannedVertices (encodeInput (lengthInstance I) ε) p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [scannedVertices, AdjacencyRAM.endpoint_shift I ε p hp, ih (p + 1) (by omega)]

theorem scanned {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    scannedVertices (multiInput I ε) 4 (2 * I.graph.edges.length) =
      I.graph.edges.flatMap (fun e => [e.1, e.2]) :=
  (vertices_shift I ε _ 3 (by decide)).trans (encoded_scannedVertices (lengthInstance I) ε)

theorem setup_run (input : RAMInput) (s : Store) :
    Run input (.atoms ops) s (prepared s) 5 := by
  have h : evalAtoms input ops s = prepared s := by
    ext r <;> simp [evalAtoms, ops, prepared, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat,
      Function.update, two_mul]
  exact h ▸ run_atoms input ops s

theorem inserted_regs (s : Store) (r : ℕ) (hr : r ≠ 143 ∧ r ≠ 144 ∧ r ≠ 145 ∧ r ≠ 146) :
    (activeResult (prepared s)).nr r = (prepared s).nr r :=
  activeResult_frame_register _ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

theorem scan_run (input : RAMInput) (s : Store) (hz : s.nr 125 = 0) (hone : s.nr 126 = 1) :
    ∃ steps ≤ 24 * s.nr 122 + 14, Run input cmd s (result input s) steps := by
  obtain ⟨si, hi, hin⟩ := activeInsert_run input (prepared s) (by simpa [prepared] using hz)
  obtain ⟨sc, hc, hscan⟩ := activeScan_run input (2 * s.nr 122) (activeResult (prepared s))
    (by rw [inserted_regs _ 125 (by decide)]; simpa [prepared] using hz)
    (by rw [inserted_regs _ 126 (by decide)]; simpa [prepared] using hone)
    (by rw [inserted_regs _ 147 (by decide), inserted_regs _ 148 (by decide)]; simp [prepared, Nat.add_comm])
  exact ⟨5 + (si + sc), by omega, Run.seq (setup_run input s) (Run.seq hin hscan)⟩

theorem scan_correct {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (base array : ℕ)
    (hm : s.nr 122 = I.graph.edges.length) (hs : s.nr 123 = I.source)
    (hb : s.nr 141 = base) (ha : s.nr 142 = array) (hsep : base + I.graph.n ≤ array)
    (hone : s.nr 126 = 1) (hz : ∀ v < I.graph.n, s.nm (base + v) = 0) :
    ActiveRep I.graph.n base array (incidentVertices I) (result (multiInput I ε) s) ∧
      ∀ a, (a < base ∨ base + I.graph.n ≤ a) → (a < array ∨ array + I.graph.n ≤ a) →
        (result (multiInput I ε) s).nm a = s.nm a := by
  let p := prepared s
  let t := activeResult p
  have h0 : ActiveRep I.graph.n base array [] p :=
    ActiveRep.empty I.graph.n base array p (by simpa [p, prepared] using hb) (by simpa [p, prepared] using ha)
      (by simp [p, prepared]) hsep hz
  have hsrc : p.nr 140 = I.source := by simp [p, prepared, hs]
  have hsv : p.nr 140 < I.graph.n := hsrc ▸ I.source_valid
  have ho : p.nr 126 = 1 := by simpa [p, prepared] using hone
  have h1 := h0.insert hsv ho
  have hot : t.nr 126 = 1 := (inserted_regs s 126 (by decide)).trans ho
  have hp : t.nr 147 = 4 := (inserted_regs s 147 (by decide)).trans (by simp [prepared])
  have hv : ∀ v ∈ scannedVertices (multiInput I ε) (t.nr 147) (2 * s.nr 122), v < I.graph.n := by
    rw [hp, hm, scanned]
    intro v h
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp h
    have hend := I.graph.endpoints e he
    simp at hv
    rcases hv with rfl | rfl
    · exact hend.1
    · exact hend.2
  have horder : (scannedVertices (multiInput I ε) (t.nr 147) (2 * s.nr 122)).foldl
      stableInsert (stableInsert [] (p.nr 140)) = incidentVertices I := by
    rw [hp, hm, scanned, hsrc]
    change _ = activeVertices (lengthInstance I)
    rw [activeVertices_eq_stableFold]
    rfl
  constructor
  · have hr := activeScan_rep (multiInput I ε) (2 * s.nr 122) t I.graph.n base array _ h1 hot hv
    rw [horder] at hr
    exact hr
  · intro a hab haa
    exact (activeScan_memory_frame (multiInput I ε) (2 * s.nr 122) t I.graph.n base array _
      h1 hot hv a hab haa).trans (h0.insert_memory_frame hsv ho a hab haa)

end NearLinearRSP.TwoResources.Supplement.IncidentRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.GraphRAM
open Mission.Structured Mission.Preprocess

def ops : List Atom :=
  [ ⟨.natConst 125 0, trivial⟩, ⟨.natConst 126 1, trivial⟩, ⟨.natConst 127 2, trivial⟩,
    ⟨.inputNat 121 125, trivial⟩, ⟨.inputNat 122 126, trivial⟩, ⟨.inputNat 123 127, trivial⟩,
    ⟨.natCopy 141 170, trivial⟩, ⟨.natOp .add 142 141 121, trivial⟩,
    ⟨.natOp .add 163 142 121, trivial⟩, ⟨.natOp .add 164 163 121, trivial⟩ ]

def cmd : Cmd := .seq (.atoms ops) (.seq IncidentRAM.cmd AdjacencyRAM.scanCmd)

structure Layout {k : ℕ} (I : MultiInstance k) (base : ℕ) (s : Store) : Prop where
  nodes : s.nr 121 = I.graph.n
  edges : s.nr 122 = I.graph.edges.length
  source : s.nr 123 = I.source
  zero : s.nr 125 = 0
  one : s.nr 126 = 1
  two : s.nr 127 = 2
  flags : s.nr 141 = base
  vertices : s.nr 142 = base + I.graph.n
  heads : s.nr 163 = base + 2 * I.graph.n
  links : s.nr 164 = base + 3 * I.graph.n

theorem setup_fields {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) :
    let p := evalAtoms (multiInput I ε) ops s
    Layout I (s.nr 170) p ∧ p.nm = s.nm ∧ p.rm = s.rm ∧ p.rr = s.rr := by
  dsimp only
  constructor
  · constructor <;> simp [ops, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, multiInput]
    all_goals omega
  · exact ⟨rfl, rfl, rfl⟩

theorem graph_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store)
    (base : ℕ) (hbase : s.nr 170 = base)
    (hz : ∀ v < I.graph.n, s.nm (base + v) = 0 ∧ s.nm (base + 2 * I.graph.n + v) = 0) :
    ∃ out steps, Run (multiInput I ε) cmd s out steps ∧ Image I base out ∧
      out.rr = s.rr ∧ out.rm = s.rm ∧
      (∀ a, (a < base ∨ base + 3 * I.graph.n + I.graph.edges.length ≤ a) → out.nm a = s.nm a) ∧
      steps ≤ 35 * I.graph.edges.length + 27 := by
  let input := multiInput I ε
  let p := evalAtoms input ops s
  let t := IncidentRAM.result input p
  obtain ⟨hl, hpm, hpr, hprr⟩ := setup_fields I ε s
  rw [hbase] at hl
  obtain ⟨n, hcost, hi⟩ := IncidentRAM.scan_run input p hl.zero hl.one
  obtain ⟨hvert, hframe⟩ := IncidentRAM.scan_correct I ε p base (base + I.graph.n)
    hl.edges hl.source hl.flags hl.vertices (by omega) hl.one
    (fun v hv => (congrFun hpm _).trans (hz v hv).1)
  have regs (r : ℕ) (hr : r ∉ IncidentRAM.cmd.natWrites) : t.nr r = p.nr r := hi.nat_frame r hr
  have hheads : ∀ v < I.graph.n, t.nm (base + 2 * I.graph.n + v) = 0 := by
    intro v hv
    exact (hframe _ (by omega) (by omega)).trans ((congrFun hpm _).trans (hz v hv).2)
  obtain ⟨out, hrun, hadj, hor, hom, hmem, hregs⟩ :=
    AdjacencyRAM.scan_correct I ε t (base + 2 * I.graph.n) (base + 3 * I.graph.n)
      ((regs 122 (by decide)).trans hl.edges) ((regs 126 (by decide)).trans hl.one)
      ((regs 127 (by decide)).trans hl.two) ((regs 163 (by decide)).trans hl.heads)
      ((regs 164 (by decide)).trans hl.links) (by omega) hheads
  have hactive : ActiveRep I.graph.n base (base + I.graph.n) (incidentVertices I) out := by
    apply hvert.congr
    · exact hregs 141 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregs 142 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hregs 143 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · intro v hv; exact hmem _ (by omega) (by omega)
    · intro v hv
      have hn := hvert.length_le
      exact hmem _ (by omega) (by omega)
  have htr : t.rr = p.rr := funext fun r => hi.real_frame r (by
    change r ∉ (∅ : Finset ℕ); simp)
  have htm : t.rm = p.rm := hi.realMemory_frame rfl
  refine ⟨out, 10 + (n + (11 * I.graph.edges.length + 3)),
    Run.seq (run_atoms input ops s) (Run.seq hi hrun), ⟨hactive, hadj⟩,
    hor.trans (htr.trans hprr), hom.trans (htm.trans hpr), ?_, ?_⟩
  · intro a ha
    exact (hmem a (by omega) (by omega)).trans
      ((hframe a (by omega) (by omega)).trans (congrFun hpm a))
  · have he : p.nr 122 = I.graph.edges.length := hl.edges
    omega

end NearLinearRSP.TwoResources.Supplement.GraphRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped NNReal BigOperators

namespace NearLinearRSP.TwoResources.Supplement

theorem pop_other_vertex {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (S : MultiLayer A.d) (v : ℕ) (j : Fin A.d → ℕ) (hv : v ∉ S.queue) :
    (pop A i S).table v j = S.table v j := by
  by_cases hn : S.queue = []
  · simp [pop, hn]
  · rw [pop_of_nonempty A i S hn, relaxAll_table]
    exact put_other _ _ _ _ _ _ (Or.inl (fun h => hv (h.symm ▸ picked_mem A S hn)))

theorem runQueue_other_vertex {k : ℕ} (A : ClockCall k) (i : Fin A.d → ℕ)
    (n : ℕ) (S : MultiLayer A.d) (v : ℕ) (j : Fin A.d → ℕ) (hv : v ∉ S.queue) :
    (runQueue A i n S).table v j = S.table v j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runQueue_succ]
    have hn : v ∉ (runQueue A i n S).queue :=
      fun hm => hv ((runQueue_queue_sublist A i n S).subset hm)
    exact (pop_other_vertex A i _ v j hn).trans ih

theorem constructTable_other_vertex {k : ℕ} (A : ClockCall k) (v : ℕ)
    (hv : v ∉ incidentVertices A.I) (j : Fin A.d → ℕ) :
    constructTable A v j = ⟨1, .none, 0⟩ := by
  apply fold_preserves (constructLayer A) (fun T => T v j = ⟨1, .none, 0⟩)
    _ _ rfl
  intro i hi T hT
  exact (runQueue_other_vertex A i _ (initializeLayer A T i) v j hv).trans hT

theorem accepts_incident {k : ℕ} (A : ClockCall k) (v : ℕ) (ha : accepts A v = true) :
    v ∈ incidentVertices A.I := by
  classical
  by_contra hv
  have he : value A (constructTable A) v (fun _ => 0) = 1 := by
    unfold value
    split_ifs
    · rfl
    · rw [constructTable_other_vertex A v hv]
  have hh : value A (constructTable A) v (fun _ => 0) ≤ 1 / 4 := by
    simpa only [accepts, decide_eq_true_eq] using ha
  rw [he] at hh
  norm_num at hh

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem guessesAux_positive (δ cap : ℝ) (hδ : 0 ≤ δ) (fuel : ℕ)
    (L : ℝ) (hL : 0 < L) (x : ℝ) (hx : x ∈ guessesAux δ cap fuel L) : 0 < x := by
  induction fuel generalizing L with
  | zero => simp [guessesAux] at hx
  | succ fuel ih =>
    simp only [guessesAux, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hL
    · split_ifs at hx with hc
      · simp at hx
      · exact ih (L * (1 + δ)) (mul_pos hL (by linarith)) hx

theorem positiveGuesses_positive {k : ℕ} (I : MultiInstance k) (ε x : ℝ)
    (hε : 0 < ε) (hx : x ∈ positiveGuesses I ε) : 0 < x := by
  unfold positiveGuesses at hx
  split_ifs at hx with h
  · simp at hx
  · exact guessesAux_positive (ε / 4) _ (by linarith) _ _
      (firstPositiveLength_pos (lengthInstance I)) x hx

theorem outerCalls_fields {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε)
    (A : ClockCall k) (hA : A ∈ outerCalls I ε) : A.I = I ∧ A.δ = ε / 4 ∧ 0 < A.L := by
  unfold outerCalls at hA
  split_ifs at hA with h
  · rcases List.mem_cons.mp hA with hA | hA
    · subst A; exact ⟨rfl, rfl, zero_lt_one⟩
    · obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hA
      exact ⟨rfl, rfl, positiveGuesses_positive I ε L hε hL⟩
  · simp at hA

theorem selectedBranch_table_accepts {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (t r : ℕ) (hb : selectedBranch I ε t = .table r) :
    ∃ A, (outerCalls I ε)[r]? = some A ∧ accepts A t = true := by
  unfold selectedBranch at hb
  split at hb
  · cases hb
  · split at hb
    · split at hb
      · cases hb
      · rename_i j hj
        have he : j = r := by simpa using hb
        subst j
        have hp := List.find?_some hj
        cases hA : (outerCalls I ε)[r]? with
        | none => simp [hA] at hp
        | some A => exact ⟨A, rfl, by simpa [hA] using hp⟩
    · split at hb <;> cases hb

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem log_ceiling_reaches (a r cap : ℝ) (ha : 0 < a) (hr : 1 < r) (hc : 0 < cap) :
    cap ≤ a * r ^ Nat.ceil (Real.log (cap / a) / Real.log r) := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 < Real.log r := Real.log_pos hr
  have hn : Real.log (cap / a) ≤
      (Nat.ceil (Real.log (cap / a) / Real.log r) : ℝ) * Real.log r :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have he := Real.exp_le_exp.mpr hn
  rw [Real.exp_log (div_pos hc ha), Real.exp_nat_mul, Real.exp_log hr0] at he
  have hh := (div_le_iff₀ ha).mp he
  simpa only [mul_comm] using hh

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
open scoped NNReal

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def callReported {k : ℕ} (ε : ℝ) (A : ClockCall k) : ℝ :=
  if A.zeroOnly then 0 else (1 + ε / 4) * A.L

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def budgetAllow {k : ℕ} (I : MultiInstance k) (u v : ℕ) : Bool :=
  decide (∀ r, I.budget r = 0 → I.cost r u v = 0)

abbrev EdgeAllowed {k : ℕ} (I : MultiInstance k) (e : ℕ × ℕ) : Prop :=
  e.1 ≠ e.2 ∧ ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0

def ShortestMatches (S : TreeQueue) (U : ShortestState) : Prop :=
  S.queue = U.queue ∧ ∀ v,
    (S.tree v).distance = (U.cells v).distance ∧ (S.tree v).parent = (U.cells v).parent

theorem distanceLess_bridge (x y : Option ℝ) :
    NearLinearRSP.TwoResources.distanceLess x y = distanceLess x y := by
  cases x <;> cases y <;> rfl

theorem shortestMatches_update (S : TreeQueue) (U : ShortestState)
    (h : ShortestMatches S U) (v : ℕ) (d : Option ℝ) (p : Option ℕ) (r : ℕ) :
    ShortestMatches { S with tree := Function.update S.tree v ⟨d, p, r⟩ }
      { U with cells := Function.update U.cells v ⟨d, p⟩ } := by
  refine ⟨h.1, ?_⟩
  intro w
  by_cases hw : w = v
  · subst w; simp
  · simpa [Function.update_of_ne hw] using h.2 w

theorem treeRelax_matches {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U)
    (e : ℕ × ℕ) (he : EdgeAllowed I e) :
    ShortestMatches (treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u S e)
      (relaxShortest I u U e) := by
  classical
  rcases he with ⟨hne, hz⟩
  have ha : budgetAllow I e.1 e.2 = true := by simpa only [budgetAllow, decide_eq_true_eq] using hz
  have hg : (e.1 = u ∧ e.1 ≠ e.2 ∧ e.2 ∈ S.queue ∧ budgetAllow I e.1 e.2 = true) ↔
      (e.1 = u ∧ e.2 ∈ U.queue) := by
    constructor
    · intro hh; exact ⟨hh.1, h.1 ▸ hh.2.2.1⟩
    · intro hh; exact ⟨hh.1, hne, h.1.symm ▸ hh.2, ha⟩
  unfold treeRelax relaxShortest
  dsimp only
  rw [if_congr hg rfl rfl]
  split_ifs with hc
  · rw [(h.2 u).1]
    cases hd : (U.cells u).distance with
    | none => exact h
    | some d =>
      dsimp only
      rw [distanceLess_bridge, (h.2 e.2).1]
      split_ifs
      · exact shortestMatches_update S U h e.2 _ _ 0
      · exact h
  · exact h

theorem treeRelax_rejected {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (S : TreeQueue) (e : ℕ × ℕ) (he : ¬EdgeAllowed I e) :
    treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u S e = S := by
  unfold treeRelax
  rw [if_neg]
  intro h
  apply he
  exact ⟨h.2.1, by simpa only [budgetAllow, decide_eq_true_eq] using h.2.2.2⟩

theorem treeRelaxFold_matches {k : ℕ} (I : MultiInstance k) (u : ℕ)
    (es : List (ℕ × ℕ)) (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches
      (es.foldl (treeRelax (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) u) S)
      ((es.filter (fun e => decide (EdgeAllowed I e))).foldl (relaxShortest I u) U) := by
  classical
  induction es generalizing S U with
  | nil => exact h
  | cons e es ih =>
    by_cases he : EdgeAllowed I e
    · have hb : decide (EdgeAllowed I e) = true := by simpa only [decide_eq_true_eq] using he
      rw [List.filter_cons, if_pos hb, List.foldl_cons, List.foldl_cons]
      exact ih _ _ (treeRelax_matches I u S U h e he)
    · have hb : ¬decide (EdgeAllowed I e) = true := by simpa only [decide_eq_true_eq] using he
      rw [List.filter_cons, if_neg hb, List.foldl_cons, treeRelax_rejected I u S e he]
      exact ih S U h

theorem treeSettle_matches (S : TreeQueue) (U : ShortestState)
    (h : ShortestMatches S U) (u : ℕ) :
    ShortestMatches (treeSettle S u) { U with queue := U.queue.erase u } := by
  refine ⟨congrArg (fun q => q.erase u) h.1, ?_⟩
  intro v
  by_cases hv : v = u
  · subst v
    simpa [treeSettle] using h.2 u
  · simpa [treeSettle, Function.update_of_ne hv] using h.2 v

theorem treePop_matches {k : ℕ} (I : MultiInstance k)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches (treePop (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) S)
      (popShortest I U) := by
  have hf : (fun x y => if NearLinearRSP.TwoResources.distanceLess
      (S.tree y).distance (S.tree x).distance then y else x) =
      (fun x y => if distanceLess (U.cells y).distance (U.cells x).distance then y else x) := by
    funext x y
    rw [distanceLess_bridge, (h.2 y).1, (h.2 x).1]
  unfold treePop popShortest
  rw [h.1]
  cases hq : U.queue with
  | nil => exact h
  | cons v vs =>
    dsimp only
    rw [hf]
    let u := (v :: vs).foldl
      (fun x y => if distanceLess (U.cells y).distance (U.cells x).distance then y else x) v
    have hm := treeRelaxFold_matches I u I.graph.edges _ _ (treeSettle_matches S U h u)
    simpa only [treeSettle, h.1, hq, usableEdges, EdgeAllowed, lengthInstance, u] using hm

theorem treeRun_matches {k : ℕ} (I : MultiInstance k) (n : ℕ)
    (S : TreeQueue) (U : ShortestState) (h : ShortestMatches S U) :
    ShortestMatches (treeRun (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) n S)
      ((List.range n).foldl (fun U _ => popShortest I U) U) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [treeRun_succ, List.range_succ, List.foldl_append]
    exact treePop_matches I _ _ ih

noncomputable def rankedShortest {k : ℕ} (I : MultiInstance k) : ShortestTree :=
  NearLinearRSP.TwoResources.shortestTree (lengthInstance I) (budgetAllow I) (fun u v => I.length u v)

theorem shortestTree_bridge {k : ℕ} (I : MultiInstance k) (v : ℕ) :
    (rankedShortest I v).distance = (shortestTree I v).distance ∧
      (rankedShortest I v).parent = (shortestTree I v).parent := by
  have hinit : ShortestMatches (treeInitial (lengthInstance I))
      ⟨fun v => ⟨if v = I.source then some 0 else none, none⟩, incidentVertices I⟩ := by
    exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  exact (treeRun_matches I (incidentVertices I).length _ _ hinit).2 v

theorem shortestTree_parent {k : ℕ} (I : MultiInstance k) (v : ℕ) (d : ℝ)
    (hv : v ≠ I.source) (hd : (shortestTree I v).distance = some d) :
    ∃ u a, (shortestTree I v).parent = some u ∧ (shortestTree I u).distance = some a ∧
      d = a + (I.length u v : ℝ) ∧ (u, v) ∈ I.graph.edges ∧ budgetAllow I u v = true ∧
      (rankedShortest I u).rank < (rankedShortest I v).rank := by
  obtain ⟨u, a, hp, ha, he, hg, hal, hr⟩ := shortestTree_finite_parent
    (lengthInstance I) (budgetAllow I) (fun u v => I.length u v) v d hv
    ((shortestTree_bridge I v).1.trans hd)
  exact ⟨u, a, ((shortestTree_bridge I v).2.symm.trans hp),
    ((shortestTree_bridge I u).1.symm.trans ha), he, hg, hal, hr⟩

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.ParentQuery

theorem incident_length_le_n {k : ℕ} (I : MultiInstance k) :
    (incidentVertices I).length ≤ I.graph.n := by
  have hnd : (incidentVertices I).Nodup := activeVertices_nodup (lengthInstance I)
  have hsub : incidentVertices I ⊆ List.range I.graph.n :=
    fun v hv => List.mem_range.mpr (incident_valid I v hv)
  simpa using hnd.length_le_of_subset hsub

end NearLinearRSP.TwoResources.Supplement.ParentQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def selectDimension (f : ℕ → Cmd) : ℕ → Cmd
  | 0 => .seq (.atom ⟨.natConst 69 0, trivial⟩) (f 0)
  | n + 1 => .seq (.atom ⟨.natConst 69 (n + 1), trivial⟩)
      (.branch (.nat .eq 68 69) (f (n + 1)) (selectDimension f n))

theorem select_dimension_run (input : RAMInput) (f : ℕ → Cmd) (n d : ℕ) (hd : d ≤ n)
    (s t : Store) (steps : ℕ) (hreg : s.nr 68 = d) (hr : Run input (f d) (marked s d) t steps) :
    ∃ cost, Run input (selectDimension f n) s t cost ∧ cost ≤ steps + 2 * n + 3 := by
  induction n generalizing s with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact ⟨_, Run.seq (Run.atom ⟨.natConst 69 0, trivial⟩ s) hr, by omega⟩
  | succ n ih =>
    let p := marked s (n + 1)
    have hp : Run input (.atom ⟨.natConst 69 (n + 1), trivial⟩) s p 1 := Run.atom _ s
    by_cases he : d = n + 1
    · rw [he] at hreg hr
      have hg : (Guard.nat .eq 68 69).eval p = true := by simp [p, marked, Guard.eval, natTest, hreg]
      exact ⟨_, Run.seq hp (Run.branchTrue hg hr), by omega⟩
    · have hg : (Guard.nat .eq 68 69).eval p = false := by simp [p, marked, Guard.eval, natTest, hreg, he]
      have hm : marked p d = marked s d := by simp [p, marked, Function.update_idem]
      obtain ⟨c, hh, hn⟩ := ih (by omega) p (by simpa [p, marked] using hreg) (hm ▸ hr)
      exact ⟨_, Run.seq hp (Run.branchFalse hg hh), by omega⟩

def dimensionOps : List Atom := [⟨.natConst 68 4, trivial⟩, ⟨.loadNat 68 68, trivial⟩]

def dimensioned (S : Store) : Store := {S with nr := Function.update S.nr 68 (S.nm 4)}

theorem dimension_run (input : RAMInput) (s : Store) :
    Run input (.atoms dimensionOps) s (dimensioned s) 2 := by
  have h : evalAtoms input dimensionOps s = dimensioned s := by
    simp [evalAtoms, dimensionOps, dimensioned, Atom.eval, Store.at, Store.ofRAM, ramStep, Function.update_idem]
  exact h ▸ run_atoms input dimensionOps s

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

noncomputable def shaped (k d : ℕ) (input : RAMInput) (s : Store) : Store :=
  added 49 60 8 (added 58 60 (d + 4) (evalAtoms input (shapeOps k) s))

theorem shape_run (k d : ℕ) (input : RAMInput) (s : Store) :
    let t := shaped k d input s
    Run input (shapeCmd k d) s t (d + 19) ∧ t.nr 58 = (d + 4) * s.nm 2 ∧ t.nr 57 = s.nm 0 ∧
      t.nr 49 = 32 + 2 * k + 8 * s.nm 2 ∧ t.nr 31 = 1 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  have he := Run.seq (run_atoms input (shapeOps k) s) (Run.seq
    (add_copies_run input 58 60 (by decide) (d + 4) (evalAtoms input (shapeOps k) s))
    (add_copies_run input 49 60 (by decide) 8 _))
  have hlen : (shapeOps k).length + ((d + 4) + 8) = d + 19 := by change 7 + ((d + 4) + 8) = _; omega
  refine ⟨hlen ▸ he, ?_⟩
  simp [shaped, added, shapeOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep]

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured TableQuery

noncomputable def callWidth {k : ℕ} (I : MultiInstance k) (ε : ℝ) :=
  4 + ((clockCoordinates I).length + 4) * I.graph.n * multiQ k ε ^ (clockCoordinates I).length

theorem address_width {k : ℕ} (I : MultiInstance k) (ε : ℝ) (j : ℕ) :
    callBase I ε j = callBase I ε 0 + callWidth I ε * j := by
  unfold callBase callWidth; ring

def widthOps : List Atom := [⟨.natConst 65 4, trivial⟩, ⟨.natOp .add 58 65 58, trivial⟩]
def dimLayout (k d : ℕ) : Cmd := .seq (SpaceRAM.shapeCmd k d) (.seq (powers d) (.atoms widthOps))
def layoutCmd (k : ℕ) : Cmd := .seq (.atoms dimensionOps) (selectDimension (dimLayout k) k)

theorem dimension_layout_run (k d : ℕ) (input : RAMInput) (s : Store) :
    ∃ t, Run input (dimLayout k d) s t (d + 21 + d * (4 * s.nm 0 + 5)) ∧
      t.nr 49 = 32 + 2 * k + 8 * s.nm 2 ∧ t.nr 58 = 4 + (d + 4) * s.nm 2 * s.nm 0 ^ d ∧
      t.nr 31 = 1 ∧ t.nm = s.nm ∧ t.rm = s.rm := by
  let p := SpaceRAM.shaped k d input s
  obtain ⟨hp, hw, hq, hb, h1, hn, hr⟩ := SpaceRAM.shape_run k d input s
  obtain ⟨w, he, hv, _, hregs, _, hnm, hrm⟩ := powers_run input p d h1
  have reg (j : ℕ) (hj : j < 58) := hregs j (fun r _ => by have := stride_large r; omega) (by omega) (by omega) (by omega)
  have h49 := (reg 49 (by decide)).trans hb
  have h31 := (reg 31 (by decide)).trans h1
  change p.nr 58 = _ at hw
  change p.nr 57 = _ at hq
  rw [hw, hq] at hv
  rw [hq] at he
  have hx := Run.seq hp (Run.seq he (run_atoms input widthOps w))
  have hc : d + 19 + (d * (4 * s.nm 0 + 5) + widthOps.length) = d + 21 + d * (4 * s.nm 0 + 5) := by
    change _ + (_ + 2) = _; omega
  refine ⟨_, hc ▸ hx, ?_⟩
  simp [widthOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, hv, h49, h31, hnm.trans hn, hrm.trans hr]

theorem layout_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (input : RAMInput) (s : Store)
    (hq : s.nm 0 = multiQ k ε) (hn : s.nm 2 = I.graph.n) (hd : s.nm 4 = (clockCoordinates I).length) :
    ∃ t n, Run input (layoutCmd k) s t n ∧ t.nr 49 = callBase I ε 0 ∧ t.nr 58 = callWidth I ε ∧
      t.nr 31 = 1 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ n ≤ 4 * k * multiQ k ε + 8 * k + 26 := by
  let d := (clockCoordinates I).length
  let p := dimensioned s
  let v := marked p d
  have hdk : d ≤ k := clockCoordinates_length_le I
  obtain ⟨t, he, ha, hw, h1, hnm, hrm⟩ := dimension_layout_run k d input v
  have hp : p.nr 68 = d := hd
  obtain ⟨n, hx, hc⟩ := select_dimension_run input (dimLayout k) k d hdk p t _ hp he
  refine ⟨t, 2 + n, Run.seq (dimension_run input s) hx, ?_, ?_, h1, hnm, hrm, ?_⟩
  · simpa only [callBase, Nat.zero_mul, Nat.add_zero, v, p, marked, dimensioned, hn] using ha
  · change t.nr 58 = 4 + (d + 4) * s.nm 2 * s.nm 0 ^ d at hw
    simpa only [callWidth, hn, hq, d] using hw
  · change n ≤ d + 21 + d * (4 * s.nm 0 + 5) + 2 * k + 3 at hc
    rw [hq] at hc
    have hm := Nat.mul_le_mul_right (multiQ k ε) hdk
    nlinarith

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured

def place {α : Type} (f : ℕ → α) (base step : ℕ) : List α → ℕ → α
  | [] => f
  | x :: xs => place (Function.update f base x) (base + step) step xs

theorem place_append {α : Type} (xs ys : List α) (f : ℕ → α) (b w : ℕ) :
    place f b w (xs ++ ys) = place (place f b w xs) (b + w * xs.length) w ys := by
  induction xs generalizing f b with
  | nil => simp [place]
  | cons x xs ih =>
    simp only [List.cons_append, place, List.length_cons]
    rw [ih, Nat.mul_succ]
    congr 1 <;> omega

theorem place_frame {α : Type} (xs : List α) (f : ℕ → α) (b w a : ℕ)
    (h : ∀ j < xs.length, a ≠ b + w * j) : place f b w xs a = f a := by
  induction xs generalizing f b with
  | nil => rfl
  | cons x xs ih =>
    have h0 : a ≠ b := by simpa using h 0 (by simp)
    have hrest : ∀ j < xs.length, a ≠ b + w + w * j := by
      intro j hj
      have hh := h (j + 1) (by simpa using hj)
      simpa only [Nat.mul_succ, Nat.add_assoc, Nat.add_comm w (w * j)] using hh
    exact (ih (Function.update f b x) (b + w) hrest).trans (Function.update_of_ne h0 _ _)

theorem place_get {α : Type} (xs : List α) (f : ℕ → α) (b w : ℕ) (hw : 0 < w) (i : ℕ)
    (hi : i < xs.length) : place f b w xs (b + w * i) = xs[i] := by
  induction xs generalizing f b i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [place, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
      rw [place_frame xs _ _ _ _ (fun j _ => by omega), Function.update_self]
    | succ i =>
      have hh := ih (Function.update f b x) (b + w) i (by simpa using hi)
      simpa [place, Nat.mul_succ, Nat.add_assoc, Nat.add_comm w (w * i)] using hh

structure Written (s t : Store) (xs : List (ℕ × ℝ)) : Prop where
  address : t.nr 49 = s.nr 49 + s.nr 58 * xs.length
  count : t.nr 52 = s.nr 52 + xs.length
  stride : t.nr 58 = s.nr 58
  naturals : t.nm = place s.nm (s.nr 49) (s.nr 58) (xs.map Prod.fst)
  reals : t.rm = place s.rm (s.nr 49) (s.nr 58) (xs.map Prod.snd)

theorem Written.nil {s t : Store} (ha : t.nr 49 = s.nr 49) (hc : t.nr 52 = s.nr 52)
    (hw : t.nr 58 = s.nr 58) (hn : t.nm = s.nm) (hr : t.rm = s.rm) : Written s t [] := by
  exact ⟨by simpa using ha, by simpa using hc, hw, hn, hr⟩

theorem Written.append {s t u : Store} {xs ys : List (ℕ × ℝ)}
    (h : Written s t xs) (g : Written t u ys) : Written s u (xs ++ ys) := by
  refine ⟨?_, ?_, g.stride.trans h.stride, ?_, ?_⟩
  · rw [g.address, h.address, h.stride, List.length_append, Nat.mul_add, Nat.add_assoc]
  · rw [g.count, h.count, List.length_append, Nat.add_assoc]
  · rw [g.naturals, h.naturals, h.address, h.stride, List.map_append, place_append, List.length_map]
  · rw [g.reals, h.reals, h.address, h.stride, List.map_append, place_append, List.length_map]

def emitOps (tag : ℕ) : List Atom :=
  [⟨.natConst 69 tag, trivial⟩, ⟨.storeNat 49 69, trivial⟩, ⟨.storeReal 49 160, trivial⟩,
   ⟨.natOp .add 49 49 58, trivial⟩, ⟨.natOp .add 52 52 31, trivial⟩]

noncomputable def emitted (input : RAMInput) (tag : ℕ) (s : Store) := evalAtoms input (emitOps tag) s

theorem emitted_written (input : RAMInput) (tag : ℕ) (s : Store) (hone : s.nr 31 = 1) :
    Written s (emitted input tag s) [(tag, s.rr 160)] := by
  constructor <;> simp [emitted, emitOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, place, hone]

theorem emitted_frame (input : RAMInput) (tag : ℕ) (s : Store) :
    let t := emitted input tag s
    t.rr = s.rr ∧ ∀ j, j ≠ 49 → j ≠ 52 → j ≠ 69 → t.nr j = s.nr j := by
  simp +contextual [emitted, emitOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep]

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured

def grow : Atom := ⟨.realOp .mul 160 160 162, trivial⟩
def stop : Atom := ⟨.natConst 53 0, trivial⟩
def guessBody : Cmd := .seq (.atoms (emitOps 0)) (.branch (.real .lt 160 161) (.atom grow) (.atom stop))
def guessLoop : Cmd := .loop (.nat .eq 53 31) guessBody

def positives (xs : List ℝ) : List (ℕ × ℝ) := xs.map (fun x => (0, x))

noncomputable def grown (input : RAMInput) (s : Store) : Store := grow.eval input (emitted input 0 s)
noncomputable def stopped (input : RAMInput) (s : Store) : Store := stop.eval input (emitted input 0 s)

theorem grow_step (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) (hlt : s.rr 160 < s.rr 161) :
    let t := grown input s
    Run input guessBody s t 8 ∧ Written s t [(0, s.rr 160)] ∧
      t.rr 160 = s.rr 160 * s.rr 162 ∧ t.rr 161 = s.rr 161 ∧ t.rr 162 = s.rr 162 ∧
      t.nr 31 = 1 ∧ t.nr 53 = s.nr 53 := by
  let p := emitted input 0 s
  obtain ⟨hr, hn⟩ := emitted_frame input 0 s
  have hg : (Guard.real .lt 160 161).eval p = true := by simp [p, Guard.eval, realTest, hr, hlt]
  have hw := emitted_written input 0 s hone
  refine ⟨Run.seq (run_atoms input (emitOps 0) s) (Run.branchTrue hg (Run.atom grow p)),
    ⟨hw.address, hw.count, hw.stride, hw.naturals, hw.reals⟩, ?_⟩
  simp [grown, grow, Atom.eval, Store.ofRAM, ramStep, Store.at, evalReal, hr, hn, hone]

theorem finish_step (input : RAMInput) (s : Store) (hone : s.nr 31 = 1) (hflag : s.nr 53 = 1)
    (hle : s.rr 161 ≤ s.rr 160) :
    Run input guessLoop s (stopped input s) 10 ∧ Written s (stopped input s) [(0, s.rr 160)] := by
  let p := emitted input 0 s
  obtain ⟨hr, hn⟩ := emitted_frame input 0 s
  have hg : (Guard.real .lt 160 161).eval p = false := by simp [p, Guard.eval, realTest, hr, not_lt.mpr hle]
  have hbody : Run input guessBody s (stopped input s) 7 :=
    Run.seq (run_atoms input (emitOps 0) s) (Run.branchFalse hg (Run.atom stop p))
  have hh := emitted_written input 0 s hone
  refine ⟨Run.loopTrue (by simp [Guard.eval, natTest, hflag, hone]) hbody (Run.loopFalse ?_),
    ⟨?_, ?_, ?_, hh.naturals, hh.reals⟩⟩
  · simp [stopped, stop, Guard.eval, natTest, Atom.eval, Store.ofRAM, ramStep, Store.at, hn, hone]
  · exact hh.address
  · exact hh.count
  · exact hh.stride

theorem geometric_last (input : RAMInput) (δ cap L : ℝ) (s : Store) (hone : s.nr 31 = 1)
    (hflag : s.nr 53 = 1) (hL : s.rr 160 = L) (hcap : s.rr 161 = cap) (hstop : cap ≤ L) (n : ℕ) :
      ∃ t, Run input guessLoop s t (10 * (guessesAux δ cap (n + 1) L).length) ∧
        Written s t (positives (guessesAux δ cap (n + 1) L)) := by
    obtain ⟨he, hw⟩ := finish_step input s hone hflag (by simpa [hcap, hL] using hstop)
    exact ⟨_, by simpa [guessesAux, hstop] using he, by simpa [guessesAux, hstop, positives, hL] using hw⟩

theorem geometric_run (input : RAMInput) (δ cap : ℝ) (fuel : ℕ) (L : ℝ) (s : Store)
    (hone : s.nr 31 = 1) (hflag : s.nr 53 = 1) (hL : s.rr 160 = L)
    (hcap : s.rr 161 = cap) (hratio : s.rr 162 = 1 + δ)
    (reach : cap ≤ L * (1 + δ) ^ fuel) :
    let xs := guessesAux δ cap (fuel + 1) L
    ∃ t, Run input guessLoop s t (10 * xs.length) ∧ Written s t (positives xs) := by
  dsimp only
  induction fuel generalizing L s with
  | zero =>
    exact geometric_last input δ cap L s hone hflag hL hcap (by simpa using reach) 0
  | succ n ih =>
    by_cases hf : cap ≤ L
    · exact geometric_last input δ cap L s hone hflag hL hcap hf (n + 1)
    · let p := grown input s
      obtain ⟨hg, hw, hpL, hpc, hpr, hp1, hpf⟩ := grow_step input s hone (by simpa [hL, hcap] using lt_of_not_ge hf)
      have hnext : p.rr 160 = L * (1 + δ) := hpL.trans (by rw [hL, hratio])
      have hreach : cap ≤ (L * (1 + δ)) * (1 + δ) ^ n := by
        simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using reach
      obtain ⟨t, ht, hmem⟩ := ih (L * (1 + δ)) p hp1 (hpf.trans hflag) hnext (hpc.trans hcap) (hpr.trans hratio) hreach
      refine ⟨t, ?_, ?_⟩
      · have hr : Run input guessLoop s t (1 + 8 + 1 + 10 * (guessesAux δ cap (n + 1) (L * (1 + δ))).length) := Run.loopTrue (show (Guard.nat .eq 53 31).eval s = true by simp [Guard.eval, natTest, hone, hflag]) hg ht
        have hxs : guessesAux δ cap (n + 1 + 1) L = L :: guessesAux δ cap (n + 1) (L * (1 + δ)) := by rw [guessesAux, if_neg hf]
        rw [hxs, List.length_cons, Nat.mul_succ]
        convert hr using 1 <;> omega
      · simpa only [hL, List.singleton_append, positives, guessesAux, if_neg hf, List.map_cons] using hw.append hmem

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.InputValues

def row (k i : ℕ) := k + k * i

theorem row_coordinate {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) (j : Fin k) :
    (multiInput I ε).reals (row k i + j.val) = coordinateWeight I j e.1 e.2 := by
  have hk : 0 < k := Nat.zero_lt_of_lt j.isLt
  have h1 : row k i + j.val ≠ 0 := by unfold row; omega
  have h2 : ¬ row k i + j.val < k := by unfold row; omega
  have hsub : row k i + j.val - k = j.val + k * i := by unfold row; omega
  have hd : (j.val + k * i) / k = i := by simp [Nat.add_mul_div_left, hk, Nat.div_eq_of_lt j.isLt]
  have hm : (j.val + k * i) % k = j.val := by simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp only [multiInput, h1, ↓reduceDIte, h2, hsub, hd, he, hm, j.isLt]

theorem row_length {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) : (multiInput I ε).reals (row k i) = I.length e.1 e.2 := by
  simpa only [Nat.add_zero, coordinateWeight, ↓reduceDIte] using row_coordinate I ε i e he ⟨0, hk⟩

theorem row_cost {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) (r : Fin (k - 1)) :
    (multiInput I ε).reals (row k i + (r.val + 1)) = I.cost r e.1 e.2 := by
  have h : r.val + 1 < k := by omega
  simpa [coordinateWeight] using row_coordinate I ε i e he ⟨r.val + 1, h⟩

theorem budget_read {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : Fin (k - 1)) :
    (multiInput I ε).reals (r.val + 1) = I.budget r := by
  have h : r.val + 1 < k := by omega
  simp [multiInput, h]

theorem edge_endpoints {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) :
    (multiInput I ε).naturals (4 + 2 * i) = e.1 ∧
    (multiInput I ε).naturals (4 + 2 * i + 1) = e.2 := by
  have hs : 4 + 2 * i + 1 - 4 = 2 * i + 1 := by omega
  have ht : 4 + 2 * i - 4 = 2 * i := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  have hm : (2 * i + 1) % 2 = 1 := by omega
  simp [multiInput, hs, ht, hd, hm, he, show 4 + 2 * i ≠ 1 by omega, show 4 + 2 * i ≠ 2 by omega,
    show 4 + 2 * i ≠ 3 by omega, show 4 + 2 * i + 1 ≠ 2 by omega, show 4 + 2 * i + 1 ≠ 3 by omega]

theorem budget_flag {k : ℕ} (I : MultiInstance k) (hk : 0 < k) :
    hasPositiveBudget I = true ↔ 1 < (clockCoordinates I).length := by
  have hzero : (⟨0, hk⟩ : Fin k) ∈ clockCoordinates I := (clockCoordinates_mem I _).mpr (Or.inl rfl)
  have hn := clockCoordinates_nodup I
  constructor
  · intro h
    obtain ⟨r, hr⟩ : ∃ r, 0 < I.budget r := by simpa [hasPositiveBudget] using h
    let j : Fin k := ⟨r.val + 1, by omega⟩
    have hj : j ∈ clockCoordinates I := (clockCoordinates_mem I j).mpr (Or.inr (by simpa [j, coordinateBudget] using hr))
    have hn2 : ([⟨0, hk⟩, j] : List (Fin k)).Nodup := by simp [j, Fin.ext_iff]
    have hsub : [⟨0, hk⟩, j] ⊆ clockCoordinates I := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hzero
      · exact hj
    have hh : 2 ≤ (clockCoordinates I).length := by simpa using (hn2.subperm hsub).length_le
    omega
  · intro hlen
    have hex : ∃ j ∈ clockCoordinates I, j.val ≠ 0 := by
      by_contra! h
      have hsub : clockCoordinates I ⊆ [⟨0, hk⟩] := fun j hj => by simpa using Fin.ext (h j hj)
      have hle := List.Subperm.length_le (hn.subperm hsub)
      exact (not_le.mpr hlen) (by simpa using hle)
    obtain ⟨j, hj, hj0⟩ := hex
    have hpos := (clockCoordinates_mem I j).mp hj |>.resolve_left hj0
    have hh : 0 < I.budget ⟨j.val - 1, by omega⟩ := by exact_mod_cast (show 0 < (I.budget ⟨j.val - 1, by omega⟩ : ℝ) by simpa [coordinateBudget, hj0] using hpos)
    simpa only [hasPositiveBudget, decide_eq_true_eq] using (show ∃ r, 0 < I.budget r from ⟨_, hh⟩)

end NearLinearRSP.TwoResources.Supplement.InputValues

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured

def copyMin : Atom := ⟨.realCopy 160 150, trivial⟩
def activeCmd : Cmd := .seq (.atoms (emitOps 1))
  (.branch (.nat .eq 150 31) (.seq (.atom copyMin) guessLoop) .skip)
def outerCmd : Cmd := .branch (.nat .lt 31 68) activeCmd .skip

noncomputable def entries {k : ℕ} (I : MultiInstance k) (ε : ℝ) : List (ℕ × ℝ) :=
  (outerCalls I ε).map (fun A => (if A.zeroOnly then 1 else 0, A.L))

structure Args {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  one : s.nr 31 = 1
  live : s.nr 53 = 1
  dimension : s.nr 68 = (clockCoordinates I).length
  found : s.nr 150 = if (positiveLengths (lengthInstance I)).isEmpty then 0 else 1
  minimum : s.rr 150 = firstPositiveLength (lengthInstance I)
  current : s.rr 160 = 1
  cap : s.rr 161 = (I.graph.n : ℝ) * largestLength (lengthInstance I)
  ratio : s.rr 162 = 1 + ε / 4

theorem positive_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (s : Store)
    (hone : s.nr 31 = 1) (hflag : s.nr 53 = 1) (hmin : s.rr 160 = firstPositiveLength (lengthInstance I))
    (hcap : s.rr 161 = (I.graph.n : ℝ) * largestLength (lengthInstance I)) (hr : s.rr 162 = 1 + ε / 4)
    (hne : positiveLengths (lengthInstance I) ≠ []) :
    ∃ t, Run (multiInput I ε) guessLoop s t (10 * (positiveGuesses I ε).length) ∧
      Written s t (positives (positiveGuesses I ε)) := by
  let a := firstPositiveLength (lengthInstance I)
  let c := (I.graph.n : ℝ) * largestLength (lengthInstance I)
  let r := 1 + ε / 4
  let n := Nat.ceil (Real.log (c / a) / Real.log r)
  have ha : 0 < a := firstPositiveLength_pos _
  have hh : 0 < r := by unfold r; linarith
  have hge : 1 < r := by unfold r; linarith
  have hn : (0 : ℝ) < I.graph.n := by exact_mod_cast (show 0 < I.graph.n by have := I.source_valid; omega)
  have hc : 0 < c := mul_pos hn (largestLength_pos _ hne)
  have hreach : c ≤ a * r ^ (n + 1) := by
    have hh0 := log_ceiling_reaches a r c ha hge hc
    have hpos : 0 ≤ a * r ^ n := by positivity
    have hmul := le_mul_of_one_le_right hpos hge.le
    rw [pow_succ, ← mul_assoc]
    exact hh0.trans hmul
  have hdef : positiveGuesses I ε = guessesAux (ε / 4) c (n + 1 + 1) a := by
    simp [positiveGuesses, List.isEmpty_iff, hne, not_le.mpr hε, a, c, n, r]
  rw [hdef]
  exact geometric_run (multiInput I ε) (ε / 4) c (n + 1) a s hone hflag hmin hcap hr hreach

theorem outer_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    (s : Store) (h : Args I ε s) :
    ∃ t n, Run (multiInput I ε) outerCmd s t n ∧ Written s t (entries I ε) ∧ n ≤ 10 * (outerCalls I ε).length + 10 := by
  let input := multiInput I ε
  by_cases hbud : hasPositiveBudget I = true
  · have hg : (Guard.nat .lt 31 68).eval s = true := by
      simp [Guard.eval, natTest, h.one, h.dimension, (InputValues.budget_flag I hk).mp hbud]
    let p := emitted input 1 s
    have he : Run input (.atoms (emitOps 1)) s p 5 := run_atoms input (emitOps 1) s
    have hw := emitted_written input 1 s h.one
    obtain ⟨hr, hn⟩ := emitted_frame input 1 s
    have hp1 : p.nr 31 = 1 := (hn 31 (by decide) (by decide) (by decide)).trans h.one
    have hpf : p.nr 53 = 1 := (hn 53 (by decide) (by decide) (by decide)).trans h.live
    have hp150 := (hn 150 (by decide) (by decide) (by decide)).trans h.found
    have hentry : entries I ε = (1, 1) :: positives (positiveGuesses I ε) := by
      simp [entries, outerCalls, hbud, positives, List.map_map, Function.comp_def]
    by_cases hne : positiveLengths (lengthInstance I) = []
    · have hz : (Guard.nat .eq 150 31).eval p = false := by simp [p, Guard.eval, natTest, hp150, hp1, hne]
      have hxs : positiveGuesses I ε = [] := by simp [positiveGuesses, hne]
      refine ⟨p, 1 + (5 + (1 + 0)) + 1, Run.branchTrue hg (Run.seq he (Run.branchFalse hz (Run.skip p))), ?_, by omega⟩
      simpa only [hentry, hxs, positives, List.map_nil, h.current] using hw
    · have hg2 : (Guard.nat .eq 150 31).eval p = true := by
        simp [p, Guard.eval, natTest, hp150, hp1, List.isEmpty_iff, hne]
      let v := copyMin.eval input p
      have hx : v = {p with rr := Function.update p.rr 160 (p.rr 150)} := rfl
      obtain ⟨t, ht, hmem⟩ := positive_run I ε hε v hp1 hpf (by simp [hx, p, hr, h.minimum])
        (by simpa [hx, p, hr] using h.cap) (by simpa [hx, p, hr] using h.ratio) hne
      have hcopy : Written p v [] := Written.nil rfl rfl rfl rfl rfl
      refine ⟨t, _, Run.branchTrue hg (Run.seq he (Run.branchTrue hg2 (Run.seq (Run.atom copyMin p) ht))), ?_, ?_⟩
      · simpa only [hentry, h.current, List.nil_append, List.singleton_append] using hw.append (hcopy.append hmem)
      · simp [outerCalls, hbud]; omega
  · have hd : ¬ 1 < (clockCoordinates I).length := fun h' => hbud ((InputValues.budget_flag I hk).mpr h')
    have hg : (Guard.nat .lt 31 68).eval s = false := by simp [Guard.eval, natTest, h.one, h.dimension, hd]
    refine ⟨s, 1, Run.branchFalse hg (Run.skip s), ?_, by omega⟩
    simpa [entries, outerCalls, hbud] using (Written.nil (s := s) rfl rfl rfl rfl rfl)

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LengthScan
open Mission.Structured Mission.Scan

def initOps (k : ℕ) : List Atom :=
  [⟨.natConst 158 1, trivial⟩, ⟨.inputNat 159 158, trivial⟩, ⟨.natConst 150 0, trivial⟩,
   ⟨.natConst 151 k, trivial⟩, ⟨.natConst 152 0, trivial⟩, ⟨.natConst 153 0, trivial⟩,
   ⟨.natConst 154 1, trivial⟩, ⟨.natConst 157 k, trivial⟩, ⟨.realConst 150 1, trivial⟩,
   ⟨.realConst 151 0, trivial⟩, ⟨.realConst 156 0, trivial⟩]
def readWeight : Atom := ⟨.inputReal 154 151, trivial⟩
def advance : List Atom := [⟨.natOp .add 151 151 157, trivial⟩, ⟨.natOp .add 152 152 154, trivial⟩]
def body : Cmd := .seq (.atom readWeight) (.seq positiveCmd (.seq (maxCmd 151 154) (.atoms advance)))
def loop : Cmd := .loop (.nat .lt 152 159) body
def cmd (k : ℕ) : Cmd := .seq (.atoms (initOps k)) loop

noncomputable def lengthPrefix {k : ℕ} (I : MultiInstance k) (j : ℕ) : Summary :=
  summarize ((I.graph.edges.take j).map (fun e => ((I.length e.1 e.2 : ℝ), (0 : ℝ))))

theorem prefix_succ {k : ℕ} (I : MultiInstance k) (j : ℕ) (hj : j < I.graph.edges.length) :
    lengthPrefix I (j + 1) = addSample (lengthPrefix I j) ((I.length I.graph.edges[j].1 I.graph.edges[j].2 : ℝ), 0) := by
  unfold lengthPrefix
  rw [List.take_succ_eq_append_getElem hj, List.map_append, List.map_singleton, addSample_summarize]

structure Rep {k : ℕ} (I : MultiInstance k) (j : ℕ) (s : Store) : Prop where
  count : s.nr 152 = j
  stop : s.nr 159 = I.graph.edges.length
  ptr : s.nr 151 = InputValues.row k j
  width : s.nr 157 = k
  zero : s.nr 153 = 0
  one : s.nr 154 = 1
  realZero : s.rr 156 = 0
  found : s.nr 150 = if (lengthPrefix I j).found then 1 else 0
  low : s.rr 150 = (lengthPrefix I j).minimum
  high : s.rr 151 = (lengthPrefix I j).maximum

theorem init_rep {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) :
    Rep I 0 (evalAtoms (multiInput I ε) (initOps k) s) := by
  constructor <;> simp [initOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, lengthPrefix,
    summarize, positives, multiInput, InputValues.row]

theorem step_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (j : ℕ) (hj : j < I.graph.edges.length)
    (s : Store) (h : Rep I j s) :
    ∃ t cost, Run (multiInput I ε) body s t cost ∧ Rep I (j + 1) t ∧ cost ≤ 12 := by
  let input := multiInput I ε
  let p := readWeight.eval input s
  let z := positiveResult input p
  let w := maxResult z 151 154
  let t := evalAtoms input advance w
  have hw : input.reals (s.nr 151) = (I.length I.graph.edges[j].1 I.graph.edges[j].2 : ℝ) := by
    rw [h.ptr]
    exact InputValues.row_length I hk ε j _ (List.getElem?_eq_getElem hj)
  have hp : p = {s with rr := Function.update s.rr 154 (input.reals (s.nr 151))} := rfl
  obtain ⟨n, hn, hex⟩ := positiveCmd_run input p h.zero (by simpa [hp] using h.realZero)
  obtain ⟨m, hm, hmax⟩ := maxCmd_run input z 151 154
  refine ⟨t, 1 + (n + (m + 2)), Run.seq (Run.atom readWeight s) (Run.seq hex (Run.seq hmax
    (run_atoms input advance w))), ?_, by omega⟩
  have hptr : s.nr 151 + k = InputValues.row k (j + 1) := by
    rw [h.ptr]; unfold InputValues.row; ring
  cases hf : (lengthPrefix I j).found <;>
    by_cases hpos : 0 < (I.length I.graph.edges[j].1 I.graph.edges[j].2 : ℝ) <;>
    constructor <;> simp [t, w, z, hp, maxResult, positiveResult, minResult, firstPositiveOps, advance,
      evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, hw, hpos, h.found, h.low, h.high,
      hptr, h.count, h.stop, h.width, h.zero, h.one, h.realZero, prefix_succ I j hj, addSample, hf]

theorem loop_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (rem j : ℕ)
    (hrem : j + rem = I.graph.edges.length) (s : Store) (h : Rep I j s) :
    ∃ t n, Run (multiInput I ε) loop s t n ∧ Rep I I.graph.edges.length t ∧ n ≤ 14 * rem + 1 := by
  induction rem generalizing j s with
  | zero =>
    have hh : j = I.graph.edges.length := by omega
    exact ⟨s, 1, Run.loopFalse (by simp [Guard.eval, natTest, h.count, h.stop, hh]), hh ▸ h, by omega⟩
  | succ rem ih =>
    have hj : j < I.graph.edges.length := by omega
    obtain ⟨p, n, ha, hp, hn⟩ := step_run I hk ε j hj s h
    obtain ⟨t, m, hb, ht, hm⟩ := ih (j + 1) (by omega) p hp
    exact ⟨t, _, Run.loopTrue (by simp [Guard.eval, natTest, h.count, h.stop, hj]) ha hb, ht, by omega⟩

theorem extrema_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (s : Store) :
    ∃ out n, Run (multiInput I ε) (cmd k) s out n ∧
      out.nr 150 = (if (positiveLengths (lengthInstance I)).isEmpty then 0 else 1) ∧
      out.rr 150 = firstPositiveLength (lengthInstance I) ∧ out.rr 151 = largestLength (lengthInstance I) ∧
      out.nm = s.nm ∧ out.rm = s.rm ∧ n ≤ 14 * I.graph.edges.length + 12 := by
  let input := multiInput I ε
  obtain ⟨t, m, hr, ht, hc⟩ := loop_run I hk ε I.graph.edges.length 0 (by omega) _ (init_rep I ε s)
  have hrun : Run input (cmd k) s t (11 + m) := Run.seq (run_atoms input (initOps k) s) hr
  have he : lengthPrefix I I.graph.edges.length = summarize (edgeSamples (lengthInstance I)) := by
    simp [lengthPrefix, edgeSamples, lengthInstance]
  obtain ⟨hf, hl, hh, _⟩ := summarize_edgeSamples (lengthInstance I)
  refine ⟨t, _, hrun, ?_, by simpa only [he, hl] using ht.low, by simpa only [he, hh] using ht.high,
    hrun.natMemory_frame rfl, hrun.realMemory_frame rfl, by omega⟩
  rw [ht.found, he, hf]
  cases (positiveLengths (lengthInstance I)).isEmpty <;> rfl

end NearLinearRSP.TwoResources.Supplement.LengthScan

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured

def readN : List Atom := [⟨.natConst 60 2, trivial⟩, ⟨.loadNat 60 60, trivial⟩]
def argsOps : List Atom :=
  [⟨.natConst 30 0, trivial⟩, ⟨.natConst 52 0, trivial⟩, ⟨.natConst 53 1, trivial⟩,
   ⟨.natConst 67 4, trivial⟩, ⟨.loadNat 68 67, trivial⟩, ⟨.inputReal 162 30, trivial⟩,
   ⟨.realConst 163 4, trivial⟩, ⟨.realOp .div 162 162 163, trivial⟩, ⟨.realConst 160 1, trivial⟩,
   ⟨.realOp .add 162 160 162, trivial⟩, ⟨.realOp .mul 161 60 151, trivial⟩]

def params (k : ℕ) : Cmd :=
  .seq (layoutCmd k) (.seq (LengthScan.cmd k) (.seq (.atoms readN) (.seq Mission.NatToReal.convertCmd (.atoms argsOps))))

def setupCost (k n m q : ℕ) :=
  (4 * k * q + 8 * k + 26) + (14 * m + 12) + (14 * (Nat.log 2 n + 1) ^ 2 + 5) + 13

theorem args_fields {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store)
    (h1 : s.nr 31 = 1) (hd : s.nm 4 = (clockCoordinates I).length)
    (hf : s.nr 150 = if (positiveLengths (lengthInstance I)).isEmpty then 0 else 1)
    (hl : s.rr 150 = firstPositiveLength (lengthInstance I)) (hh : s.rr 151 = largestLength (lengthInstance I))
    (hn : s.rr 60 = (I.graph.n : ℝ)) :
    Args I ε (evalAtoms (multiInput I ε) argsOps s) := by
  constructor <;> simp [argsOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalReal,
    h1, hd, hf, hl, hh, hn, multiInput]

theorem params_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (s : Store)
    (hq : s.nm 0 = multiQ k ε) (hn : s.nm 2 = I.graph.n) (hd : s.nm 4 = (clockCoordinates I).length) :
    ∃ t n, Run (multiInput I ε) (params k) s t n ∧ Args I ε t ∧ t.nr 49 = callBase I ε 0 ∧
      t.nr 58 = callWidth I ε ∧ t.nr 52 = 0 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      n ≤ setupCost k I.graph.n I.graph.edges.length (multiQ k ε) := by
  let input := multiInput I ε
  obtain ⟨p, a, hp, hpb, hpw, hp1, hpn, hpr, hca⟩ := layout_run I ε input s hq hn hd
  obtain ⟨u, b, hu, huf, hul, huh, hun, hur, hcb⟩ := LengthScan.extrema_run I hk ε p
  let x := evalAtoms input readN u
  have hx : x = {u with nr := Function.update u.nr 60 (u.nm 2)} := by
    simp [x, readN, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_idem]
  have xu : x.nr 60 = I.graph.n := by simp [hx, hun, hpn, hn]
  obtain ⟨y, c, hy, hyr, hcc, hframe⟩ := Mission.NatToReal.convertCmd_run input x
  obtain ⟨ynr, yrr, ynm, yrm⟩ := hframe
  let t := evalAtoms input argsOps y
  have h31 : y.nr 31 = 1 := (ynr 31 (by omega)).trans ((hu.nat_frame 31 (by change 31 ∉ (LengthScan.cmd 0).natWrites; decide)).trans hp1)
  have h49 : y.nr 49 = callBase I ε 0 := (ynr 49 (by omega)).trans ((hu.nat_frame 49 (by change 49 ∉ (LengthScan.cmd 0).natWrites; decide)).trans hpb)
  have h58 : y.nr 58 = callWidth I ε := (ynr 58 (by omega)).trans ((hu.nat_frame 58 (by change 58 ∉ (LengthScan.cmd 0).natWrites; decide)).trans hpw)
  have h150 : y.nr 150 = u.nr 150 := ynr 150 (by omega)
  have yN : y.nm = s.nm := ynm.trans (hun.trans hpn)
  have yR : y.rm = s.rm := yrm.trans (hur.trans hpr)
  have ha := args_fields I ε y h31 ((congrFun yN 4).trans hd) (h150.trans huf)
    ((yrr 150 (by decide) (by decide)).trans hul) ((yrr 151 (by decide) (by decide)).trans huh)
    (hyr.trans (by rw [xu]))
  have he : Run input (params k) s t (a + (b + (2 + (c + 11)))) :=
    Run.seq hp (Run.seq hu (Run.seq (run_atoms input readN u) (Run.seq hy (run_atoms input argsOps y))))
  refine ⟨t, _, he, ha, ?_, ?_, ?_, yN, yR, ?_⟩
  · exact h49
  · exact h58
  · rfl
  · rw [xu] at hcc
    unfold setupCost
    omega

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.CallRAM
open Mission.Structured

def sealOps : List Atom := [⟨.natConst 65 5, trivial⟩, ⟨.storeNat 65 52, trivial⟩, ⟨.natCopy 170 49, trivial⟩]
def buildCmd (k : ℕ) : Cmd := .seq (params k) (.seq outerCmd (.atoms sealOps))

structure CallImage {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  count : s.nm 5 = (outerCalls I ε).length
  bounds : ∀ r A, (outerCalls I ε)[r]? = some A →
    s.nm (callBase I ε r) = (if A.zeroOnly then 1 else 0) ∧ s.rm (callBase I ε r) = A.L

theorem headers_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (s : Store)
    (hq : s.nm 0 = multiQ k ε) (hn : s.nm 2 = I.graph.n) (hd : s.nm 4 = (clockCoordinates I).length) :
    ∃ t cost, Run (multiInput I ε) (buildCmd k) s t cost ∧ CallImage I ε t ∧
      t.nr 170 = callBase I ε (outerCalls I ε).length ∧
      (∀ a, a ≠ 5 → (∀ j < (outerCalls I ε).length, a ≠ callBase I ε j) → t.nm a = s.nm a) ∧
      (∀ a, (∀ j < (outerCalls I ε).length, a ≠ callBase I ε j) → t.rm a = s.rm a) ∧
      cost ≤ setupCost k I.graph.n I.graph.edges.length (multiQ k ε) + 10 * (outerCalls I ε).length + 13 := by
  let input := multiInput I ε
  obtain ⟨p, a, hp, hargs, hbase, hwidth, h0, hnmem, hrmem, hca⟩ := params_run I hk ε s hq hn hd
  obtain ⟨w, b, hw, himage, hcb⟩ := outer_run I hk ε hε p hargs
  let t := evalAtoms input sealOps w
  have hlen : (entries I ε).length = (outerCalls I ε).length := by simp [entries]
  have hc : w.nr 52 = (outerCalls I ε).length := by simpa [h0, hlen] using himage.count
  have ha : w.nr 49 = callBase I ε (outerCalls I ε).length := by
    simpa only [hbase, hwidth, hlen, address_width I ε (outerCalls I ε).length] using himage.address
  have htm : t.nm = Function.update w.nm 5 (outerCalls I ε).length := by
    simp [t, sealOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, hc]
  have htr : t.rm = w.rm := rfl
  have hptr : t.nr 170 = callBase I ε (outerCalls I ε).length := ha
  have hwpos : 0 < p.nr 58 := by rw [hwidth]; unfold callWidth; omega
  refine ⟨t, a + (b + 3), Run.seq hp (Run.seq hw (run_atoms input sealOps w)), ⟨?_, ?_⟩, hptr, ?_, ?_, by omega⟩
  · simp [htm]
  · intro r A hA
    obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hA
    have hne : callBase I ε r ≠ 5 := by unfold callBase; omega
    have hi' : r < (entries I ε).length := by rwa [hlen]
    have htag := place_get ((entries I ε).map Prod.fst) p.nm (p.nr 49) (p.nr 58) hwpos r (by simpa using hi')
    have hval := place_get ((entries I ε).map Prod.snd) p.rm (p.nr 49) (p.nr 58) hwpos r (by simpa using hi')
    rw [htm, Function.update_of_ne hne, htr, himage.naturals, himage.reals]
    rw [hbase, hwidth, ← address_width] at htag hval
    exact ⟨by simpa [entries, hget, hbase, hwidth] using htag, by simpa [entries, hget, hbase, hwidth] using hval⟩
  · intro j hj hfree
    rw [htm, Function.update_of_ne hj, himage.naturals]
    apply Eq.trans (place_frame _ _ _ _ _ ?_) (congrFun hnmem j)
    intro i hi
    simpa only [hbase, hwidth, ← address_width] using hfree i (by simpa only [List.length_map, hlen] using hi)
  · intro j hfree
    rw [htr, himage.reals]
    apply Eq.trans (place_frame _ _ _ _ _ ?_) (congrFun hrmem j)
    intro i hi
    simpa only [hbase, hwidth, ← address_width] using hfree i (by simpa only [List.length_map, hlen] using hi)

end NearLinearRSP.TwoResources.Supplement.CallRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.CoordinateRAM
open Mission.Structured

noncomputable def active (input : RAMInput) (r : ℕ) : Bool := decide (r = 0 ∨ 0 < input.reals r)

def loadOps (r : ℕ) : List Atom :=
  [ ⟨.natConst 21 r, trivial⟩, ⟨.inputReal 20 21, trivial⟩, ⟨.realConst 21 0, trivial⟩ ]

def appendOps : List Atom :=
  [ ⟨.natOp .add 24 22 20, trivial⟩, ⟨.storeNat 24 21, trivial⟩,
    ⟨.natOp .add 20 20 23, trivial⟩ ]

def stepCmd (r : ℕ) : Cmd :=
  .seq (Cmd.atoms (loadOps r))
    (if r = 0 then Cmd.atoms appendOps else
      .branch (.real .lt 21 20) (Cmd.atoms appendOps) .skip)

def scanCmd : List ℕ → Cmd
  | [] => .skip
  | r :: rs => .seq (stepCmd r) (scanCmd rs)

structure Records (xs : List ℕ) (s : Store) : Prop where
  count : s.nr 20 = xs.length
  base : s.nr 22 = 8
  one : s.nr 23 = 1
  values : ∀ j (hj : j < xs.length), s.nm (8 + j) = xs[j]

structure MemoryFrame (s t : Store) : Prop where
  header : ∀ a, a < 8 → t.nm a = s.nm a
  reals : t.rm = s.rm

theorem MemoryFrame.refl (s : Store) : MemoryFrame s s := ⟨fun _ _ => rfl, rfl⟩

theorem MemoryFrame.trans {s t u : Store} (h : MemoryFrame s t) (g : MemoryFrame t u) :
    MemoryFrame s u := ⟨fun a ha => (g.header a ha).trans (h.header a ha), g.reals.trans h.reals⟩

theorem load_fields (input : RAMInput) (r : ℕ) (s : Store) :
    let t := evalAtoms input (loadOps r) s
    t.nr 21 = r ∧ t.rr 20 = input.reals r ∧ t.rr 21 = 0 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ a, a ≠ 21 → t.nr a = s.nr a) := by
  simp +contextual [loadOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, Function.update_apply]

theorem load_records (input : RAMInput) (r : ℕ) (s : Store) (xs : List ℕ) (h : Records xs s) :
    Records xs (evalAtoms input (loadOps r) s) := by
  obtain ⟨hr, hx, hz, hm, _, hn⟩ := load_fields input r s
  exact ⟨(hn 20 (by decide)).trans h.count, (hn 22 (by decide)).trans h.base,
    (hn 23 (by decide)).trans h.one, fun j hj => by rw [hm]; exact h.values j hj⟩

theorem append_records (input : RAMInput) (s : Store) (xs : List ℕ) (h : Records xs s) :
    Records (xs ++ [s.nr 21]) (evalAtoms input appendOps s) := by
  have he : evalAtoms input appendOps s =
      { s with
        nr := Function.update (Function.update s.nr 24 (8 + xs.length)) 20 (xs.length + 1)
        nm := Function.update s.nm (8 + xs.length) (s.nr 21) } := by
    simp [appendOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, h.base, h.count, h.one]
  refine ⟨by simp [he], by simpa [he] using h.base, by simpa [he] using h.one, ?_⟩
  intro j hj
  by_cases hjlt : j < xs.length
  · rw [List.getElem_append_left hjlt]
    have hne : 8 + j ≠ 8 + xs.length := by omega
    simpa [he, Function.update_of_ne hne] using h.values j hjlt
  · have hjEq : j = xs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    simp [he]

theorem append_frame (input : RAMInput) (s : Store) (hbase : s.nr 22 = 8) :
    MemoryFrame s (evalAtoms input appendOps s) := by
  constructor
  · intro a ha
    have hne : a ≠ 8 + s.nr 20 := by omega
    simp [appendOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalNat, hbase,
      Function.update_of_ne hne]
  · rfl

theorem step_run (input : RAMInput) (r : ℕ) (s : Store) (xs : List ℕ) (h : Records xs s) :
    ∃ t steps, Run input (stepCmd r) s t steps ∧
      Records (xs ++ if active input r then [r] else []) t ∧ MemoryFrame s t ∧ steps ≤ 8 := by
  let v := evalAtoms input (loadOps r) s
  obtain ⟨hvr, hvx, hvz, hvm, hvrm, hvn⟩ := load_fields input r s
  change v.nr 21 = r at hvr
  change v.rr 20 = input.reals r at hvx
  change v.rr 21 = 0 at hvz
  have hvrec := load_records input r s xs h
  have hvframe : MemoryFrame s v := ⟨fun _ _ => congrFun hvm _, hvrm⟩
  have hload : Run input (Cmd.atoms (loadOps r)) s v 3 := run_atoms input (loadOps r) s
  by_cases hr : r = 0
  · have ha : active input r = true := by simp [active, hr]
    refine ⟨evalAtoms input appendOps v, 6, ?_, ?_, hvframe.trans (append_frame input v hvrec.base), by decide⟩
    · simpa only [stepCmd, if_pos hr, show appendOps.length = 3 from rfl] using Run.seq hload (run_atoms input appendOps v)
    · simpa [ha, hvr] using append_records input v xs hvrec
  · by_cases hx : 0 < input.reals r
    · have ha : active input r = true := by simp [active, hx]
      have hg : (Guard.real .lt 21 20).eval v = true := by
        simpa only [Guard.eval, realTest, hvx, hvz, decide_eq_true_eq] using hx
      refine ⟨evalAtoms input appendOps v, 8, ?_, ?_, hvframe.trans (append_frame input v hvrec.base), by decide⟩
      · simpa only [stepCmd, if_neg hr, show appendOps.length = 3 from rfl] using Run.seq hload
          (Run.branchTrue hg (run_atoms input appendOps v))
      · simpa [ha, hvr] using append_records input v xs hvrec
    · have ha : active input r = false := by simp [active, hr, hx]
      have hg : (Guard.real .lt 21 20).eval v = false := by
        simpa only [Guard.eval, realTest, hvx, hvz, decide_eq_false_iff_not] using hx
      refine ⟨v, 4, ?_, ?_, hvframe, by decide⟩
      · simpa only [stepCmd, if_neg hr] using Run.seq hload (Run.branchFalse hg (Run.skip v))
      · simpa [ha] using hvrec

theorem scan_run (input : RAMInput) (rs : List ℕ) (s : Store) (xs : List ℕ) (h : Records xs s) :
    ∃ t steps, Run input (scanCmd rs) s t steps ∧ Records (xs ++ rs.filter (active input)) t ∧
      MemoryFrame s t ∧ steps ≤ 8 * rs.length := by
  induction rs generalizing s xs with
  | nil => exact ⟨s, 0, Run.skip s, by simpa using h, MemoryFrame.refl s, by simp⟩
  | cons r rs ih =>
    obtain ⟨v, n, hrun, hrec, hframe, hn⟩ := step_run input r s xs h
    obtain ⟨t, m, hrun', hrec', hframe', hm⟩ := ih v _ hrec
    refine ⟨t, n + m, Run.seq hrun hrun', ?_, hframe.trans hframe', ?_⟩
    · cases ha : active input r <;> simpa [List.filter_cons, ha, List.append_assoc] using hrec'
    · simp only [List.length_cons]; omega

end NearLinearRSP.TwoResources.Supplement.CoordinateRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.ScalarRAM
open Mission.Structured

def prefixOps (k : ℕ) : List Atom :=
  [ ⟨.natConst 0 0, trivial⟩,
    ⟨.inputReal 0 0, trivial⟩,
    ⟨.realOp .mul 10 0 0, trivial⟩,
    ⟨.realConst 13 (8192 * (k : ℝ)), trivial⟩,
    ⟨.realOp .div 10 13 10, trivial⟩,
    ⟨.natConst 11 1, trivial⟩,
    ⟨.realConst 11 1, trivial⟩,
    ⟨.natConst 10 0, trivial⟩,
    ⟨.realConst 12 0, trivial⟩ ]

def tickBody : List Atom :=
  [ ⟨.realOp .add 12 12 11, trivial⟩, ⟨.natOp .add 10 10 11, trivial⟩ ]

def tickLoop : Cmd := .loop (.real .lt 12 10) (Cmd.atoms tickBody)

noncomputable def counterState (s : Store) (j : ℕ) : Store :=
  { s with nr := Function.update s.nr 10 j, rr := Function.update s.rr 12 j }

def suffix (k : ℕ) : List Atom :=
  [ ⟨.natConst 0 0, trivial⟩, ⟨.storeNat 0 10, trivial⟩,
    ⟨.natConst 0 2, trivial⟩, ⟨.inputNat 1 0, trivial⟩,
    ⟨.natConst 0 1, trivial⟩, ⟨.storeNat 0 1, trivial⟩,
    ⟨.natConst 0 0, trivial⟩, ⟨.inputNat 1 0, trivial⟩,
    ⟨.natConst 0 2, trivial⟩, ⟨.storeNat 0 1, trivial⟩,
    ⟨.natConst 0 3, trivial⟩, ⟨.natConst 1 k, trivial⟩, ⟨.storeNat 0 1, trivial⟩,
    ⟨.realConst 1 8, trivial⟩, ⟨.realOp .div 2 0 1, trivial⟩,
    ⟨.realOp .add 2 11 2, trivial⟩, ⟨.realConst 1 4, trivial⟩,
    ⟨.realOp .div 3 0 1, trivial⟩, ⟨.realOp .add 3 11 3, trivial⟩,
    ⟨.realOp .div 2 2 3, trivial⟩,
    ⟨.natConst 0 0, trivial⟩, ⟨.storeReal 0 2, trivial⟩,
    ⟨.realConst 1 (8 * (k : ℝ)), trivial⟩, ⟨.realOp .div 2 11 1, trivial⟩,
    ⟨.natConst 0 1, trivial⟩, ⟨.storeReal 0 2, trivial⟩ ]

def scalarCmd (k : ℕ) : Cmd :=
  .seq (Cmd.atoms (prefixOps k)) (.seq tickLoop (Cmd.atoms (suffix k)))

def ScalarHeader {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState) : Prop :=
  S.nm 0 = multiQ k ε ∧ S.nm 1 = I.source ∧ S.nm 2 = I.graph.n ∧ S.nm 3 = k ∧
    S.rm 0 = (1 + ε / 8) / (1 + ε / 4) ∧ S.rm 1 = 1 / (8 * (k : ℝ))

theorem prefix_fields (k : ℕ) (input : RAMInput) (s : Store) :
    let t := evalAtoms input (prefixOps k) s
    t.nr 10 = 0 ∧ t.nr 11 = 1 ∧ t.rr 0 = input.reals 0 ∧
      t.rr 10 = 8192 * (k : ℝ) / (input.reals 0) ^ 2 ∧ t.rr 11 = 1 ∧ t.rr 12 = 0 := by
  simp [prefixOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalReal, pow_two]

theorem tickBody_eval (input : RAMInput) (s : Store) (j : ℕ)
    (hn : s.nr 11 = 1) (hr : s.rr 11 = 1) :
    evalAtoms input tickBody (counterState s j) = counterState s (j + 1) := by
  apply Store.ext <;> funext a
  all_goals simp [tickBody, counterState, evalAtoms, Atom.eval, Store.ofRAM, ramStep,
    Store.at, evalNat, evalReal, Function.update_apply, hn, hr, Nat.cast_add, Nat.cast_one]

theorem tickLoop_run (input : RAMInput) (s : Store) (j n : ℕ)
    (hn : s.nr 11 = 1) (hr : s.rr 11 = 1) (hj : j + n = Nat.ceil (s.rr 10)) :
    Run input tickLoop (counterState s j) (counterState s (Nat.ceil (s.rr 10))) (4 * n + 1) := by
  induction n generalizing j with
  | zero =>
    have he : j = Nat.ceil (s.rr 10) := by omega
    rw [he]
    apply Run.loopFalse
    simp only [Guard.eval, realTest, counterState, Function.update_self,
      Function.update_of_ne (by decide : 10 ≠ 12), decide_eq_false_iff_not]
    exact not_lt.mpr (Nat.le_ceil _)
  | succ n ih =>
    have hlt : (j : ℝ) < s.rr 10 := Nat.lt_ceil.mp (by omega)
    have hg : (Guard.real .lt 12 10).eval (counterState s j) = true := by
      simpa [Guard.eval, realTest, counterState] using hlt
    have hb : Run input (Cmd.atoms tickBody) (counterState s j) (counterState s (j + 1)) 2 := by
      simpa only [tickBody_eval input s j hn hr, show tickBody.length = 2 from rfl] using
        run_atoms input tickBody (counterState s j)
    rw [show 4 * (n + 1) + 1 = 1 + 2 + 1 + (4 * n + 1) by omega]
    exact Run.loopTrue hg hb (ih (j + 1) (by omega))

theorem suffix_fields (k : ℕ) (input : RAMInput) (s : Store) (hr : s.rr 11 = 1) :
    let t := evalAtoms input (suffix k) s
    t.nm 0 = s.nr 10 ∧ t.nm 1 = input.naturals 2 ∧ t.nm 2 = input.naturals 0 ∧ t.nm 3 = k ∧
      t.rm 0 = (1 + s.rr 0 / 8) / (1 + s.rr 0 / 4) ∧ t.rm 1 = 1 / (8 * (k : ℝ)) := by
  simp [suffix, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, evalReal, hr]

theorem scalar_run (k : ℕ) (input : RAMInput) (s : Store) :
    ∃ t, Run input (scalarCmd k) s t (36 + 4 * Nat.ceil (8192 * (k : ℝ) / (input.reals 0) ^ 2)) ∧
      t.nm 0 = Nat.ceil (8192 * (k : ℝ) / (input.reals 0) ^ 2) ∧
      t.nm 1 = input.naturals 2 ∧ t.nm 2 = input.naturals 0 ∧ t.nm 3 = k ∧
      t.rm 0 = (1 + input.reals 0 / 8) / (1 + input.reals 0 / 4) ∧ t.rm 1 = 1 / (8 * (k : ℝ)) := by
  let p := evalAtoms input (prefixOps k) s
  obtain ⟨hn0, hn1, hε, hx, hr1, hr0⟩ := prefix_fields k input s
  have hp : counterState p 0 = p := by
    apply Store.ext <;> try rfl
    · funext a; simp only [counterState, Function.update_apply]; split_ifs with he
      · subst a; exact hn0.symm
      · rfl
    · funext a; simp only [counterState, Function.update_apply]; split_ifs with he
      · subst a; simpa using hr0.symm
      · rfl
  let q := Nat.ceil (p.rr 10)
  have hq : q = Nat.ceil (8192 * (k : ℝ) / (input.reals 0) ^ 2) := congrArg Nat.ceil hx
  have hpε : p.rr 0 = input.reals 0 := hε
  have hloop : Run input tickLoop p (counterState p q) (4 * q + 1) := by
    simpa only [hp] using tickLoop_run input p 0 q hn1 hr1 (by simp [q])
  let t := evalAtoms input (suffix k) (counterState p q)
  refine ⟨t, ?_, ?_⟩
  · have hrun := Run.seq (run_atoms input (prefixOps k) s)
      (Run.seq hloop (run_atoms input (suffix k) (counterState p q)))
    have heq : 36 + 4 * Nat.ceil (8192 * (k : ℝ) / (input.reals 0) ^ 2) =
        (prefixOps k).length + (4 * q + 1 + (suffix k).length) := by
      simp only [prefixOps, suffix, List.length_cons, List.length_nil, hq]
      omega
    rw [heq]
    exact hrun
  · have hh := suffix_fields k input (counterState p q) (by simpa [counterState] using hr1)
    change t.nm 0 = q ∧ t.nm 1 = input.naturals 2 ∧ t.nm 2 = input.naturals 0 ∧ t.nm 3 = k ∧
      t.rm 0 = (1 + p.rr 0 / 8) / (1 + p.rr 0 / 4) ∧ t.rm 1 = 1 / (8 * (k : ℝ)) at hh
    rw [hq, hpε] at hh
    exact hh

end NearLinearRSP.TwoResources.Supplement.ScalarRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.CoordinateRAM
open Mission.Structured

def initOps : List Atom :=
  [ ⟨.natConst 20 0, trivial⟩, ⟨.natConst 22 8, trivial⟩, ⟨.natConst 23 1, trivial⟩ ]

def finishOps : List Atom :=
  [ ⟨.natConst 24 4, trivial⟩, ⟨.storeNat 24 20, trivial⟩ ]

def coordinateCmd (k : ℕ) : Cmd :=
  .seq (Cmd.atoms initOps) (.seq (scanCmd (List.range k)) (Cmd.atoms finishOps))

theorem initial_records (input : RAMInput) (s : Store) :
    Records [] (evalAtoms input initOps s) := by
  constructor
  all_goals simp [initOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at]

theorem finish_fields (input : RAMInput) (s : Store) :
    let t := evalAtoms input finishOps s
    t.nm 4 = s.nr 20 ∧ (∀ a, a ≠ 4 → t.nm a = s.nm a) ∧ t.rm = s.rm := by
  simp +contextual [finishOps, evalAtoms, Atom.eval, Store.ofRAM, ramStep, Store.at, Function.update_apply]

theorem coordinate_run (k : ℕ) (input : RAMInput) (s : Store) :
    ∃ t steps, Run input (coordinateCmd k) s t steps ∧
      t.nm 4 = ((List.range k).filter (active input)).length ∧
      (∀ j (hj : j < ((List.range k).filter (active input)).length),
        t.nm (8 + j) = ((List.range k).filter (active input))[j]) ∧
      (∀ a, a < 4 → t.nm a = s.nm a) ∧ t.rm = s.rm ∧ steps ≤ 8 * k + 5 := by
  let p := evalAtoms input initOps s
  obtain ⟨v, n, hrun, hrec, hframe, hc⟩ := scan_run input (List.range k) p [] (initial_records input s)
  have hcount : v.nr 20 = ((List.range k).filter (active input)).length := by simpa using hrec.count
  have hvalues : ∀ j (hj : j < ((List.range k).filter (active input)).length),
      v.nm (8 + j) = ((List.range k).filter (active input))[j] := by simpa using hrec.values
  let t := evalAtoms input finishOps v
  obtain ⟨h4, hother, hr⟩ := finish_fields input v
  refine ⟨t, initOps.length + (n + finishOps.length),
    Run.seq (run_atoms input initOps s) (Run.seq hrun (run_atoms input finishOps v)),
    h4.trans hcount, ?_, ?_, hr.trans hframe.reals, ?_⟩
  · intro j hj
    exact (hother (8 + j) (by omega)).trans (hvalues j hj)
  · intro a ha
    exact (hother a (by omega)).trans (hframe.header a (by omega))
  · simp only [List.length_range] at hc
    simp only [initOps, finishOps, List.length_cons, List.length_nil]
    omega

theorem active_coordinates {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    (List.range k).filter (active (multiInput I ε)) = (clockCoordinates I).map Fin.val := by
  have hmap : (List.finRange k).map Fin.val = List.range k := by
    ext i <;> simp
  rw [← hmap, List.filter_map]
  unfold clockCoordinates
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro r hr
  by_cases hz : r.val = 0
  · simp [active, Function.comp_def, hz]
  · simp [active, Function.comp_def, coordinateBudget, multiInput, hz, r.isLt]

def setupCmd (k : ℕ) : Cmd := .seq (ScalarRAM.scalarCmd k) (coordinateCmd k)

def InputHeader {k : ℕ} (I : MultiInstance k) (ε : ℝ) (S : RAMState) : Prop :=
  ScalarRAM.ScalarHeader I ε S ∧ S.nm 4 = (clockCoordinates I).length ∧
    ∀ r : Fin (clockCoordinates I).length, S.nm (8 + r.val) = ((clockCoordinates I).get r).val

end NearLinearRSP.TwoResources.Supplement.CoordinateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

namespace NearLinearRSP.TwoResources.Supplement.HeaderFrame
open Mission.Structured CoordinateRAM

theorem scalar_far {k : ℕ} {input : RAMInput} {s t : Store} {n : ℕ}
    (h : Run input (ScalarRAM.scalarCmd k) s t n) :
    (∀ a, 4 ≤ a → t.nm a = s.nm a) ∧ (∀ a, 2 ≤ a → t.rm a = s.rm a) := by
  cases h with
  | seq hp hrest =>
    cases hrest with
    | seq hl he =>
      have hh := Mission.Queue.run_final_unique he (run_atoms input (ScalarRAM.suffix k) _)
      subst t
      have hpn := hp.natMemory_frame rfl
      have hpr := hp.realMemory_frame rfl
      have hln := hl.natMemory_frame rfl
      have hlr := hl.realMemory_frame rfl
      constructor
      · intro a ha
        simp [ScalarRAM.suffix, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
          Function.update_of_ne (show a ≠ 0 by omega), Function.update_of_ne (show a ≠ 1 by omega),
          Function.update_of_ne (show a ≠ 2 by omega), Function.update_of_ne (show a ≠ 3 by omega), hln, hpn]
      · intro a ha
        simp [ScalarRAM.suffix, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep,
          Function.update_of_ne (show a ≠ 0 by omega), Function.update_of_ne (show a ≠ 1 by omega), hlr, hpr]

theorem append_far (input : RAMInput) (s : Store) (a : ℕ) (hne : a ≠ s.nr 22 + s.nr 20) :
    (evalAtoms input appendOps s).nm a = s.nm a := by
  simp [appendOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat, Function.update_of_ne hne]

theorem step_far (input : RAMInput) (r : ℕ) (s t : Store) (n a : ℕ)
    (h : Run input (stepCmd r) s t n) (hne : a ≠ s.nr 22 + s.nr 20) : t.nm a = s.nm a := by
  cases h with
  | seq hload hb =>
    rename_i u n m
    have he := Mission.Queue.run_final_unique hload (run_atoms input (loadOps r) s)
    let p := evalAtoms input (loadOps r) s
    have hu : u = p := he
    subst u
    have hh (v : Store) (cost : ℕ) (happ : Run input (.atoms appendOps) p v cost) : v.nm a = s.nm a := by
      rw [Mission.Queue.run_final_unique happ (run_atoms input appendOps p)]
      exact append_far input p a hne
    split at hb
    · exact hh _ _ hb
    · cases hb with
      | branchTrue _ hr => exact hh _ _ hr
      | branchFalse _ hr => cases hr; rfl

theorem scan_far (input : RAMInput) (rs xs : List ℕ) (s t : Store) (n a : ℕ)
    (h : Records xs s) (hr : Run input (scanCmd rs) s t n) (ha : 8 + xs.length + rs.length ≤ a) :
    t.nm a = s.nm a := by
  induction rs generalizing xs s t n with
  | nil => cases hr; rfl
  | cons r rs ih =>
    cases hr with
    | seq hstep htail =>
      obtain ⟨v, c, hh, hv, _, _⟩ := step_run input r s xs h
      have he := Mission.Queue.run_final_unique hstep hh
      subst v
      have hlen : (xs ++ if active input r then [r] else []).length ≤ xs.length + 1 := by
        cases active input r <;> simp
      have ha' : 8 + xs.length + (rs.length + 1) ≤ a := by simpa using ha
      have hhead := step_far input r s _ _ a hstep (by rw [h.base, h.count]; omega)
      exact (ih _ _ _ _ hv htail (by omega)).trans hhead

theorem coordinate_far {k : ℕ} {input : RAMInput} {s t : Store} {n : ℕ}
    (h : Run input (coordinateCmd k) s t n) (a : ℕ) (ha : 8 + k ≤ a) : t.nm a = s.nm a := by
  cases h with
  | seq hp hr =>
    cases hr with
    | seq hscan he =>
      have hpre := Mission.Queue.run_final_unique hp (run_atoms input initOps s)
      have hh := Mission.Queue.run_final_unique he (run_atoms input finishOps _)
      subst t
      have hrec := hpre.symm ▸ initial_records input s
      have hfar := scan_far input (List.range k) [] _ _ _ a hrec hscan (by simpa using ha)
      exact ((finish_fields input _).2.1 a (by omega)).trans (hfar.trans (congrFun (hp.natMemory_frame rfl) a))

theorem setup_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) :
    ∃ t n, Run (multiInput I ε) (setupCmd k) s t n ∧ InputHeader I ε (t.at 0) ∧
      (∀ a, 8 + k ≤ a → t.nm a = s.nm a) ∧ (∀ a, 2 ≤ a → t.rm a = s.rm a) ∧ n ≤ 4 * multiQ k ε + 8 * k + 41 := by
  let input := multiInput I ε
  obtain ⟨p, hp, hq, hs, hn, hk, hz, hH⟩ := ScalarRAM.scalar_run k input s
  obtain ⟨t, n, ht, hd, hm, hf, hr, hc⟩ := coordinate_run k input p
  have hceil : Nat.ceil (8192 * (k : ℝ) / ε ^ 2) = multiQ k ε := by
    unfold multiQ ticks; congr 1; field_simp; ring
  have hε : input.reals 0 = ε := by simp [input, multiInput]
  have he := Run.seq hp ht
  obtain ⟨hfn, hfr⟩ := scalar_far hp
  refine ⟨t, _, he, ⟨?_, ?_, ?_⟩, fun a ha => (coordinate_far ht a ha).trans (hfn a (by omega)),
    fun a ha => (congrFun hr a).trans (hfr a ha), ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hf 0 (by decide)).trans (hq.trans (by rw [hε, hceil]))
    · simpa [hf 1 (by decide), input, multiInput, Store.at] using hs
    · simpa [hf 2 (by decide), input, multiInput, Store.at] using hn
    · exact (hf 3 (by decide)).trans hk
    · simpa [Store.at, hr, hε] using hz
    · simpa [Store.at, hr] using hH
  · simpa [Store.at, input, active_coordinates] using hd
  · intro r
    have hv := hm r.val (by simpa only [input, active_coordinates, List.length_map] using r.isLt)
    simpa only [Store.at, input, active_coordinates, List.getElem_map, List.get_eq_getElem] using hv
  · rw [hε, hceil]
    omega

end NearLinearRSP.TwoResources.Supplement.HeaderFrame

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.PrepareRAM
open Mission.Structured

noncomputable def privateBase {k : ℕ} (I : MultiInstance k) (ε : ℝ) := callBase I ε (outerCalls I ε).length

theorem call_increasing {k : ℕ} (I : MultiInstance k) (ε : ℝ) {i j : ℕ} (h : i < j) :
    callBase I ε i < callBase I ε j := by
  rw [CallRAM.address_width I ε i, CallRAM.address_width I ε j]
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h (by unfold CallRAM.callWidth; omega)) _

theorem call_lower {k : ℕ} (I : MultiInstance k) (ε : ℝ) (j : ℕ) :
    32 + 2 * k ≤ callBase I ε j := by unfold callBase; omega

def cmd (k : ℕ) : Cmd := .seq (CoordinateRAM.setupCmd k) (.seq (CallRAM.buildCmd k) GraphRAM.cmd)

structure Prepared {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  header : CoordinateRAM.InputHeader I ε (s.at 0)
  calls : CallRAM.CallImage I ε s
  base : s.nr 170 = privateBase I ε
  graph : GraphRAM.Image I (privateBase I ε) s
  natZero : ∀ a, 8 + k ≤ a → (∀ j < (outerCalls I ε).length, a ≠ callBase I ε j) →
    (a < privateBase I ε ∨ privateBase I ε + 3 * I.graph.n + I.graph.edges.length ≤ a) → s.nm a = 0
  realZero : ∀ a, 2 ≤ a → (∀ j < (outerCalls I ε).length, a ≠ callBase I ε j) → s.rm a = 0

def bound (k n m q calls : ℕ) := (4 * q + 8 * k + 41) + (CallRAM.setupCost k n m q + 10 * calls + 13) + (35 * m + 27)

theorem prepare_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∃ s n, Run (multiInput I ε) (cmd k) initialStore s n ∧ Prepared I ε s ∧
      n ≤ bound k I.graph.n I.graph.edges.length (multiQ k ε) (outerCalls I ε).length := by
  obtain ⟨p, n, hp, hheader, hpn, hpr, hn⟩ := HeaderFrame.setup_run I ε initialStore
  obtain ⟨hh, hd, hcoords⟩ := hheader
  obtain ⟨hq, hsrc, hN, hK, hz, hH⟩ := hh
  obtain ⟨w, c, hw, hc, hb, hwn, hwr, hcost⟩ := CallRAM.headers_run I hk ε hε p hq hN hd
  let b := privateBase I ε
  have hb' : w.nr 170 = b := hb
  have hmin : 32 + 2 * k ≤ b := call_lower I ε _
  have hlo (j : ℕ) (hj : j < (outerCalls I ε).length) : callBase I ε j < b := call_increasing I ε hj
  have hfree (a : ℕ) (ha : b ≤ a) : w.nm a = 0 :=
    (hwn a (by omega) (fun j hj => by have := hlo j hj; omega)).trans (hpn a (by omega))
  obtain ⟨s, g, hg, hi, _, hgr, hgn, hgc⟩ := GraphRAM.graph_run I ε w b hb'
    (fun v _ => ⟨hfree _ (by omega), hfree _ (by omega)⟩)
  have hsmall (a : ℕ) (ha : a < 32 + 2 * k) (h5 : a ≠ 5) : s.nm a = p.nm a :=
    (hgn a (Or.inl (by omega))).trans (hwn a h5 (fun j _ => by have := call_lower I ε j; omega))
  have hreal (a : ℕ) (ha : a < 32 + 2 * k) : s.rm a = p.rm a :=
    (congrFun hgr a).trans (hwr a (fun j _ => by have := call_lower I ε j; omega))
  have hsbase : s.nr 170 = b := (hg.nat_frame 170 (by decide)).trans hb'
  refine ⟨s, n + (c + g), Run.seq hp (Run.seq hw hg), ⟨?_, ?_, hsbase, hi, ?_, ?_⟩, ?_⟩
  · refine ⟨⟨(hsmall 0 (by omega) (by decide)).trans hq, (hsmall 1 (by omega) (by decide)).trans hsrc,
      (hsmall 2 (by omega) (by decide)).trans hN, (hsmall 3 (by omega) (by decide)).trans hK,
      (hreal 0 (by omega)).trans hz, (hreal 1 (by omega)).trans hH⟩, (hsmall 4 (by omega) (by decide)).trans hd, ?_⟩
    intro j
    have hh := j.isLt
    have hdk := clockCoordinates_length_le I
    exact (hsmall _ (by omega) (by omega)).trans (hcoords j)
  · refine ⟨(hgn 5 (Or.inl (by omega))).trans hc.count, ?_⟩
    intro r A hr
    have hlt := hlo r (List.getElem?_eq_some_iff.mp hr).1
    obtain ⟨hflag, hlen⟩ := hc.bounds r A hr
    exact ⟨(hgn _ (Or.inl hlt)).trans hflag, (congrFun hgr _).trans hlen⟩
  · intro a ha hf hside
    exact (hgn _ hside).trans ((hwn a (by omega) hf).trans (hpn a ha))
  · intro a ha hf
    exact (congrFun hgr _).trans ((hwr a hf).trans (hpr a ha))
  · unfold bound
    omega

end NearLinearRSP.TwoResources.Supplement.PrepareRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement

noncomputable def thresholdLog {k : ℕ} (I : MultiInstance k) : ℝ :=
  1 + Real.log ((max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I))

theorem thresholdLog_ge_one {k : ℕ} (I : MultiInstance k) : 1 ≤ thresholdLog I := by
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hr := one_le_aspectRatio (lengthInstance I)
  have hprod : 1 ≤ (max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I) := by nlinarith
  have hl := Real.log_nonneg hprod
  unfold thresholdLog
  linarith

theorem guessesAux_length_le (δ cap : ℝ) (fuel : ℕ) (L : ℝ) :
    (guessesAux δ cap fuel L).length ≤ fuel := by
  induction fuel generalizing L with
  | zero => simp [guessesAux]
  | succ n ih =>
    rw [guessesAux]
    split_ifs
    · simp
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih (L * (1 + δ))) 1

theorem log_grid_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ε / 8 ≤ Real.log (1 + ε / 4) := by
  have hlog := Real.le_log_one_add_of_nonneg (show 0 ≤ ε / 4 by linarith)
  have hden : 0 < ε / 4 + 2 := by linarith
  have hlow : ε / 8 ≤ 2 * (ε / 4) / (ε / 4 + 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact hlow.trans hlog

theorem positiveGuesses_length_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((positiveGuesses I ε).length : ℝ) ≤ 11 * thresholdLog I / ε := by
  have hlog := thresholdLog_ge_one I
  unfold positiveGuesses
  split_ifs with hempty
  · simp only [List.length_nil, Nat.cast_zero]
    exact div_nonneg (by linarith) hε.le
  · have hne : positiveLengths (lengthInstance I) ≠ [] := by
      intro he
      apply hempty
      exact Or.inl (by simp [he])
    let a := firstPositiveLength (lengthInstance I)
    let b := largestLength (lengthInstance I)
    let y := (I.graph.n : ℝ) * b / a
    let z := Real.log (1 + ε / 4)
    have ha : 0 < a := firstPositiveLength_pos _
    have hab : a ≤ b := firstPositiveLength_le_largestLength _ hne
    have hn : (1 : ℝ) ≤ I.graph.n := by exact_mod_cast (show 1 ≤ I.graph.n by have := I.source_valid; omega)
    have hy : 1 ≤ y := by
      apply (le_div_iff₀ ha).mpr
      nlinarith
    have hR : aspectRatio (lengthInstance I) = b / a := by
      simp only [aspectRatio, List.isEmpty_iff, if_neg hne, a, b]
    have hyN : y ≤ (max 2 I.graph.n : ℕ) * aspectRatio (lengthInstance I) := by
      rw [hR]
      have hnN : (I.graph.n : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast le_max_right 2 I.graph.n
      dsimp [y]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hnN (div_nonneg (ha.le.trans hab) ha.le)
    have hln : 0 ≤ Real.log y := Real.log_nonneg hy
    have hlnN : Real.log y ≤ thresholdLog I - 1 := by
      have hh := Real.log_le_log (by linarith : 0 < y) hyN
      simpa [thresholdLog] using hh
    have hz : 0 < z := Real.log_pos (by linarith)
    have hzlow : ε / 8 ≤ z := log_grid_lower ε hε hε1
    have hratio : Real.log y / z ≤ 8 * (thresholdLog I - 1) / ε := by
      apply (div_le_iff₀ hz).mpr
      have hprod := mul_le_mul_of_nonneg_left hzlow (by linarith : 0 ≤ thresholdLog I - 1)
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hε).mpr
      have hh := mul_le_mul_of_nonneg_right hlnN hε.le
      nlinarith
    have hc := (Nat.ceil_lt_add_one (div_nonneg hln hz.le)).le
    have hlen := guessesAux_length_le (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a
    have hlenR : ((guessesAux (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a).length : ℝ) ≤ (Nat.ceil (Real.log y / z) : ℝ) + 2 := by
      exact_mod_cast hlen
    change ((guessesAux (ε / 4) ((I.graph.n : ℝ) * b)
      (Nat.ceil (Real.log y / z) + 2) a).length : ℝ) ≤ _
    have hsmall : 8 * (thresholdLog I - 1) / ε + 3 ≤ 11 * thresholdLog I / ε := by
      apply (le_div_iff₀ hε).mpr
      have hmul : (8 * (thresholdLog I - 1) / ε) * ε = 8 * (thresholdLog I - 1) := by
        field_simp
      nlinarith
    exact (hlenR.trans (by linarith)).trans hsmall

theorem outerCalls_length_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) ≤ 12 * thresholdLog I / ε := by
  have hl := positiveGuesses_length_bound I ε hε hε1
  have hlog := thresholdLog_ge_one I
  have hunit : 1 ≤ thresholdLog I / ε := (le_div_iff₀ hε).mpr (by linarith)
  unfold outerCalls
  split_ifs
  · simp only [List.length_cons, List.length_map, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ 11 * thresholdLog I / ε + thresholdLog I / ε := add_le_add hl hunit
      _ = _ := by ring
  · simp only [List.length_nil, Nat.cast_zero]
    exact div_nonneg (by linarith) hε.le

theorem multiQ_bound (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((multiQ k ε + 1 : ℕ) : ℝ) ≤ (8192 * (k : ℝ) + 2) / ε ^ 2 := by
  have he : 512 * (k : ℝ) / (ε / 4) ^ 2 = 8192 * (k : ℝ) / ε ^ 2 := by
    field_simp
    ring
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 512 * (k : ℝ) / (ε / 4) ^ 2 by positivity)).le
  rw [he] at hc
  have hh : (multiQ k ε : ℝ) ≤ 8192 * (k : ℝ) / ε ^ 2 + 1 := by
    simpa only [multiQ, ticks, he] using hc
  rw [Nat.cast_add, Nat.cast_one]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  have hmul := mul_le_mul_of_nonneg_right hh (sq_nonneg ε)
  have hcancel : (8192 * (k : ℝ) / ε ^ 2) * ε ^ 2 = 8192 * (k : ℝ) := by field_simp
  nlinarith

theorem multiQ_power_bound (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) ≤
      (8192 * (k : ℝ) + 2) ^ (2 * k) / ε ^ (4 * k) := by
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ (multiQ k ε + 1 : ℕ) by positivity)
    (multiQ_bound k ε hε hε1) (2 * k)
  rw [div_pow, ← pow_mul] at hp
  simpa only [show 2 * (2 * k) = 4 * k by omega] using hp

theorem call_grid_work_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) ≤
      (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * thresholdLog I / ε ^ (4 * k + 1) := by
  have hl := outerCalls_length_bound I ε hε hε1
  have hq := multiQ_power_bound k ε hε hε1
  have hlog := thresholdLog_ge_one I
  calc
    _ ≤ (12 * thresholdLog I / ε) * ((8192 * (k : ℝ) + 2) ^ (2 * k) / ε ^ (4 * k)) :=
      mul_le_mul hl hq (by positivity) (div_nonneg (by linarith) hε.le)
    _ = _ := by rw [pow_succ]; field_simp

theorem scaled_grid_work_bound {k : ℕ} (I : MultiInstance k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) *
      (((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k)) ≤
      (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * multiScale I ε := by
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hl := Real.log_nonneg hn
  have h := mul_le_mul_of_nonneg_left (call_grid_work_bound I ε hε hε1)
    (show 0 ≤ (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) by positivity)
  calc
    _ ≤ _ := h
    _ = _ := by unfold multiScale thresholdLog; ring

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement

theorem multiScale_lower {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) : 1 / ε ^ 2 ≤ multiScale I ε := by
  have hm : (1 : ℝ) ≤ (max 1 I.graph.edges.length : ℕ) := by exact_mod_cast le_max_left 1 I.graph.edges.length
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hl := Real.log_nonneg hn
  have hlog := thresholdLog_ge_one I
  have hprod : 1 ≤ (max 1 I.graph.edges.length : ℕ) *
      (1 + Real.log (max 2 I.graph.n : ℕ)) * thresholdLog I := by
    have hm' : 1 ≤ (max 1 I.graph.edges.length : ℕ) * (1 + Real.log (max 2 I.graph.n : ℕ)) := by nlinarith
    nlinarith
  have hp : ε ^ (4 * k + 1) ≤ ε ^ 2 := pow_le_pow_of_le_one hε.le hε1.le (by omega)
  calc
    _ ≤ 1 / ε ^ (4 * k + 1) := one_div_le_one_div_of_le (pow_pos hε _) hp
    _ ≤ _ := (div_le_div_iff_of_pos_right (pow_pos hε _)).mpr hprod

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

def reserveCoefficient (k : ℕ) : ℝ :=
  4 * (k : ℝ) * (8192 * k + 2) + (8 * k + 35) + 4 * (12 * (8192 * k + 2) ^ (2 * k))

theorem scale_one {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    1 ≤ multiScale I ε := by
  apply le_trans _ (multiScale_lower I hk ε hε hε1)
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  nlinarith [mul_pos hε (sub_pos.mpr hε1)]

theorem calls_le_scale {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((outerCalls I ε).length : ℝ) ≤ (12 * (8192 * (k : ℝ) + 2) ^ (2 * k)) * multiScale I ε := by
  have hm : (1 : ℝ) ≤ (max 1 I.graph.edges.length : ℕ) := by exact_mod_cast le_max_left 1 I.graph.edges.length
  have hn : (1 : ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hlog : 1 ≤ 1 + Real.log (max 2 I.graph.n : ℕ) := by linarith [Real.log_nonneg hn]
  have hfac := one_le_mul_of_one_le_of_one_le hm hlog
  have hq : (1 : ℝ) ≤ ((multiQ k ε + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ multiQ k ε + 1 by omega)
  have hp := one_le_pow₀ (n := 2 * k) hq
  calc
    _ ≤ ((outerCalls I ε).length : ℝ) * ((multiQ k ε + 1 : ℕ) : ℝ) ^ (2 * k) :=
      le_mul_of_one_le_right (by positivity) hp
    _ ≤ _ := (le_mul_of_one_le_left (by positivity) hfac).trans (scaled_grid_work_bound I ε hε hε1)

theorem reserve_bound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : n ≤ 4 * k * multiQ k ε + 8 * k + 35 + 4 * (outerCalls I ε).length) :
    (n : ℝ) ≤ reserveCoefficient k * multiScale I ε := by
  have hq0 := multiQ_bound k ε hε hε1
  rw [Nat.cast_add, Nat.cast_one] at hq0
  have hq : (multiQ k ε : ℝ) ≤ (8192 * (k : ℝ) + 2) * multiScale I ε := by
    calc
      _ ≤ (8192 * (k : ℝ) + 2) / ε ^ 2 := by linarith
      _ = _ * (1 / ε ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multiScale_lower I hk ε hε hε1) (by positivity)
  have ha := mul_le_mul_of_nonneg_left hq (show 0 ≤ 4 * (k : ℝ) by positivity)
  have hb := le_mul_of_one_le_right (show 0 ≤ 8 * (k : ℝ) + 35 by positivity) (scale_one I hk ε hε hε1)
  have hc := mul_le_mul_of_nonneg_left (calls_le_scale I ε hε hε1) (show (0 : ℝ) ≤ 4 by norm_num)
  have ht : (n : ℝ) ≤ 4 * (k : ℝ) * (multiQ k ε : ℝ) + 8 * k + 35 + 4 * ((outerCalls I ε).length : ℝ) := by
    exact_mod_cast hn
  unfold reserveCoefficient
  linarith only [ht, ha, hb, hc]

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.PrepareRAM
open Mission.Structured

noncomputable def logFactor : ℝ := 1 + 1 / Real.log 2

theorem graph_scales {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (I.graph.edges.length : ℝ) ≤ multiScale I ε ∧ (1 + Real.log (max 2 I.graph.n : ℕ)) ^ 2 ≤ multiScale I ε := by
  let N : ℝ := (max 2 I.graph.n : ℕ)
  let M : ℝ := (max 1 I.graph.edges.length : ℕ)
  let H := 1 + Real.log N
  have hn : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hm : 1 ≤ M := by dsimp [M]; exact_mod_cast le_max_left 1 I.graph.edges.length
  have hh : 1 ≤ H := by unfold H; linarith [Real.log_nonneg hn]
  have hratio := one_le_aspectRatio (lengthInstance I)
  have hHL : H ≤ thresholdLog I := by
    have hx := Real.log_le_log (show 0 < N by linarith) (le_mul_of_one_le_right (show 0 ≤ N by linarith) hratio)
    unfold thresholdLog H
    linarith only [hx]
  have hpos : 0 ≤ M * H * thresholdLog I :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hscale : M * H * thresholdLog I ≤ multiScale I ε := by
    change M * H * thresholdLog I ≤ (M * H * thresholdLog I) / ε ^ (4 * k + 1)
    apply (le_div_iff₀ (pow_pos hε _)).mpr
    exact mul_le_of_le_one_right hpos (pow_le_one₀ hε.le hε1.le)
  have hleft : M ≤ M * H := le_mul_of_one_le_right (by linarith) hh
  have hwhole : M * H ≤ M * H * thresholdLog I := le_mul_of_one_le_right (by linarith) (hh.trans hHL)
  have hfactor : H ≤ M * H := le_mul_of_one_le_left (by linarith) hm
  refine ⟨(show (I.graph.edges.length : ℝ) ≤ M by dsimp [M]; exact_mod_cast le_max_right 1 I.graph.edges.length).trans
    (hleft.trans (hwhole.trans hscale)), ?_⟩
  change H ^ 2 ≤ _
  rw [pow_two]
  exact (mul_le_mul hfactor hHL (by linarith) (by linarith)).trans hscale

theorem binary_log {k : ℕ} (I : MultiInstance k) :
    ((Nat.log 2 I.graph.n : ℝ) + 1) ^ 2 ≤ logFactor ^ 2 * (1 + Real.log (max 2 I.graph.n : ℕ)) ^ 2 := by
  let N : ℝ := (max 2 I.graph.n : ℕ)
  have hn : (0 : ℝ) < I.graph.n := by exact_mod_cast (show 0 < I.graph.n by have := I.source_valid; omega)
  have hnN : (I.graph.n : ℝ) ≤ N := by dsimp [N]; exact_mod_cast le_max_right 2 I.graph.n
  have hN : (1 : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_nonneg hN
  have hraw : (Nat.log 2 I.graph.n : ℝ) ≤ Real.log N / Real.log 2 :=
    (Real.natLog_le_logb I.graph.n 2).trans (div_le_div_of_nonneg_right (Real.log_le_log hn hnN) h2.le)
  have hl : (Nat.log 2 I.graph.n : ℝ) + 1 ≤ logFactor * (1 + Real.log N) := by
    unfold logFactor
    rw [div_eq_mul_inv] at hraw
    rw [one_div]
    nlinarith [inv_nonneg.mpr h2.le]
  simpa only [mul_pow] using pow_le_pow_left₀ (show (0 : ℝ) ≤ (Nat.log 2 I.graph.n : ℝ) + 1 by positivity) hl 2

noncomputable def coefficient (k : ℕ) : ℝ :=
  (4 + 4 * (k : ℝ)) * (8192 * k + 2) + 49 + 14 * logFactor ^ 2 +
    10 * (12 * (8192 * k + 2) ^ (2 * k)) + (16 * k + 137)

theorem prepare_bound {k : ℕ} (I : MultiInstance k) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (n : ℕ) (hn : n ≤ bound k I.graph.n I.graph.edges.length (multiQ k ε) (outerCalls I ε).length) :
    (n : ℝ) ≤ coefficient k * multiScale I ε := by
  have hq := multiQ_bound k ε hε hε1
  rw [Nat.cast_add, Nat.cast_one] at hq
  have hqscale : (multiQ k ε : ℝ) ≤ (8192 * (k : ℝ) + 2) * multiScale I ε := by
    calc
      _ ≤ (8192 * (k : ℝ) + 2) / ε ^ 2 := by linarith
      _ = _ * (1 / ε ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multiScale_lower I hk ε hε hε1) (by positivity)
  obtain ⟨he, hl⟩ := graph_scales I ε hε hε1
  have hb := (binary_log I).trans (mul_le_mul_of_nonneg_left hl (sq_nonneg logFactor))
  have h1 := SpaceRAM.scale_one I hk ε hε hε1
  have hconst := le_mul_of_one_le_right (show 0 ≤ 16 * (k : ℝ) + 137 by positivity) h1
  have hp := mul_le_mul_of_nonneg_left hqscale (show 0 ≤ 4 + 4 * (k : ℝ) by positivity)
  have hcalls := SpaceRAM.calls_le_scale I ε hε hε1
  have hraw : n ≤ (4 + 4 * k) * multiQ k ε + 49 * I.graph.edges.length +
      14 * (Nat.log 2 I.graph.n + 1) ^ 2 + 10 * (outerCalls I ε).length + (16 * k + 137) := by
    unfold bound CallRAM.setupCost at hn
    nlinarith only [hn]
  have hreal : (n : ℝ) ≤ (4 + 4 * (k : ℝ)) * (multiQ k ε : ℝ) + 49 * I.graph.edges.length +
      14 * ((Nat.log 2 I.graph.n : ℝ) + 1) ^ 2 + 10 * (outerCalls I ε).length + (16 * k + 137) := by
    exact_mod_cast hraw
  unfold coefficient
  linarith only [hreal, hp, he, hb, hcalls, hconst]

theorem prepare_bounded {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s n, Run (multiInput I ε) (cmd k) initialStore s n ∧ Prepared I ε s ∧ (n : ℝ) ≤ coefficient k * multiScale I ε := by
  obtain ⟨s, n, he, h, hc⟩ := prepare_run I hk ε hε
  exact ⟨s, n, he, h, prepare_bound I hk ε hε hε1 n hc⟩

end NearLinearRSP.TwoResources.Supplement.PrepareRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured

def height {k : ℕ} (I : MultiInstance k) := Nat.clog 2 (incidentVertices I).length
def capacity {k : ℕ} (I : MultiInstance k) := 2 ^ height I
noncomputable def keyBase {k : ℕ} (I : MultiInstance k) (ε : ℝ) :=
  PrepareRAM.privateBase I ε + 3 * I.graph.n + I.graph.edges.length
noncomputable def paramBase {k : ℕ} (I : MultiInstance k) (ε : ℝ) := keyBase I ε + (incidentVertices I).length
noncomputable def heapBase {k : ℕ} (I : MultiInstance k) (ε : ℝ) := paramBase I ε + 2 * k
noncomputable def parentsBase {k : ℕ} (I : MultiInstance k) (ε : ℝ) := heapBase I ε + 2 * capacity I

def countOp : Atom := ⟨.natCopy 10 143, trivial⟩
def arenaOps (k : ℕ) : List Atom :=
  [⟨.natConst 65 2, trivial⟩, ⟨.loadNat 185 65, trivial⟩, ⟨.natConst 65 1, trivial⟩, ⟨.inputNat 186 65, trivial⟩,
   ⟨.natOp .add 189 170 185, trivial⟩, ⟨.natOp .add 189 189 185, trivial⟩, ⟨.natOp .add 189 189 185, trivial⟩,
   ⟨.natOp .add 189 189 186, trivial⟩, ⟨.natOp .add 190 189 143, trivial⟩, ⟨.natConst 65 (2 * k), trivial⟩,
   ⟨.natOp .add 180 190 65, trivial⟩, ⟨.natCopy 188 11, trivial⟩, ⟨.natOp .add 181 180 188, trivial⟩,
   ⟨.natOp .add 181 181 188, trivial⟩]
def arena (k : ℕ) : Cmd := .seq (.atom countOp) (.seq Mission.Queue.chooseCapacity (.atoms (arenaOps k)))

theorem arena_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (h : PrepareRAM.Prepared I ε s) :
    ∃ t n, Run (multiInput I ε) (arena k) s t n ∧ PrepareRAM.Prepared I ε t ∧
      Config (capacity I) (heapBase I ε) (parentsBase I ε) t ∧ t.nr 189 = keyBase I ε ∧
      t.nr 190 = paramBase I ε ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ n ≤ 3 * height I + 17 := by
  let input := multiInput I ε
  let p := countOp.eval input s
  have hlen : s.nr 143 = (incidentVertices I).length := h.graph.vertices.count_reg
  have hp : p.nr 10 = (incidentVertices I).length := hlen
  let hc := Mission.Queue.chooseCapacity_exact input p
  obtain ⟨w, c, hw, hcost, hcap, hnm, hrm, _, hfr⟩ := hc
  rw [hp] at hcap hcost
  let t := evalAtoms input (arenaOps k) w
  have hbase : w.nr 170 = PrepareRAM.privateBase I ε := (hfr 170 (by decide)).trans h.base
  have hn : w.nm 2 = I.graph.n := (congrFun hnm 2).trans h.header.1.2.2.1
  have hcnt : w.nr 143 = (incidentVertices I).length := (hfr 143 (by decide)).trans hlen
  have hm : input.naturals 1 = I.graph.edges.length := by simp [input, multiInput]
  have ha : t.nr 189 = keyBase I ε ∧ t.nr 190 = paramBase I ε ∧
      t.nr 180 = heapBase I ε ∧ t.nr 181 = parentsBase I ε ∧ t.nr 188 = capacity I := by
    simp [t, arenaOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat,
      hbase, hn, hm, hcnt, hcap, keyBase, paramBase, heapBase, parentsBase, capacity, height]
    omega
  obtain ⟨hkey, hpar, hwin, hparents, hcapacity⟩ := ha
  have run : Run input (arena k) s t (1 + (c + 14)) :=
    Run.seq (Run.atom countOp s) (Run.seq hw (run_atoms input (arenaOps k) w))
  have tn : t.nm = s.nm := hnm
  have tr : t.rm = s.rm := hrm
  have h141 : t.nr 141 = s.nr 141 := run.nat_frame 141 (by change 141 ∉ (arena 0).natWrites; decide)
  have h142 : t.nr 142 = s.nr 142 := run.nat_frame 142 (by change 142 ∉ (arena 0).natWrites; decide)
  have h143 : t.nr 143 = s.nr 143 := run.nat_frame 143 (by change 143 ∉ (arena 0).natWrites; decide)
  have ha' := h.graph.vertices.congr h141 h142 h143 (fun _ _ => congrFun tn _) (fun _ _ => congrFun tn _)
  have hhead : CoordinateRAM.InputHeader I ε (t.at 0) := by
    simpa only [CoordinateRAM.InputHeader, ScalarRAM.ScalarHeader, Store.at, tn, tr] using h.header
  have hcalls : CallRAM.CallImage I ε t := ⟨(congrFun tn _).trans h.calls.count, fun j A hj => by
    simpa only [tn, tr] using h.calls.bounds j A hj⟩
  refine ⟨t, _, run, ⟨hhead, hcalls, (run.nat_frame 170 (by change 170 ∉ (arena 0).natWrites; decide)).trans h.base,
    ⟨ha', tn ▸ h.graph.outgoing⟩, fun a h1 h2 h3 => (congrFun tn a).trans (h.natZero a h1 h2 h3),
    fun a h1 h2 => (congrFun tr a).trans (h.realZero a h1 h2)⟩, ⟨hwin, hparents, hcapacity⟩,
    hkey, hpar, tn, tr, ?_⟩
  unfold height
  omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

theorem copies_preserve (dst src n a : ℕ) (ha : a ≠ dst) : a ∉ (addCopies dst src n).natWrites := by
  induction n with
  | zero => simp [addCopies, Cmd.natWrites]
  | succ n ih => simp [addCopies, Cmd.natWrites, Atom.natWrites, ih, ha]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem row_end {k : ℕ} (A : ClockCall k) (base v : ℕ) (i : Fin A.d → ℕ) (hv : v ∈ incidentVertices A.I)
    (hi : ∀ r, i r < A.q) : rowCell A base i v + 4 + A.d ≤ extent A base := by
  have h := scanAddress_inside A base v (incident_valid A.I v hv) i hi (A.d + 3) (by omega)
  change rowCell A base i v + (A.d + 3) < extent A base at h
  omega

theorem ParentRecords.congr {k : ℕ} {A : ClockCall k} {base : ℕ} {i : Fin A.d → ℕ} {p : ℕ → MultiParent}
    {s t : Store} (h : ParentRecords A base i p s) (hi : ∀ r, i r < A.q)
    (hf : ∀ a < extent A base, t.nm a = s.nm a ∧ t.rm a = s.rm a) :
    ParentRecords A base i p t := by
  intro w hw
  let a := rowCell A base i w
  have hb : a + 4 + A.d ≤ extent A base := row_end A base w i hw hi
  obtain ⟨ht, hd, hg⟩ := h w hw
  refine ⟨((hf a (by omega)).1).trans ht, ((hf (a + 1) (by omega)).1).trans hd, ?_⟩
  intro u hu r
  have hr := r.isLt
  exact ((hf (a + 4 + r.val) (by omega)).2).trans (hg u hu r)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

def Pass (input : RAMInput) (base r : ℕ) := input.reals (r + 1) = 0 → input.reals (base + (r + 1)) = 0

theorem test_fields (input : RAMInput) (r : ℕ) (s : Store) :
    let t := evalAtoms input (loadTest r) s
    t.nr 70 = s.nr 70 ∧ t.nr 71 = s.nr 71 ∧ t.rr 74 = s.rr 74 ∧
      t.rr 72 = input.reals (r + 1) ∧ t.rr 73 = input.reals (s.nr 70 + (r + 1)) := by
  simp [loadTest, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalNat]

theorem test_run (input : RAMInput) (r : ℕ) (s : Store) (hz : s.rr 74 = 0) :
    ∃ t n, Run input (test r) s t n ∧
      t.nr 71 = (if Pass input (s.nr 70) r then s.nr 71 else 0) ∧
      t.nr 70 = s.nr 70 ∧ t.rr 74 = 0 ∧ n ≤ 8 := by
  classical
  let p := evalAtoms input (loadTest r) s
  obtain ⟨ha, hflag, hzero, hb, hw⟩ := test_fields input r s
  have he : Run input (.atoms (loadTest r)) s p 4 := run_atoms input _ _
  have h0 : p.rr 74 = 0 := hzero.trans hz
  by_cases hbud : input.reals (r + 1) = 0
  · have g₁ : (Guard.real .eq 72 74).eval p = true := by simp [Guard.eval, realTest, p, hb, h0, hbud]
    by_cases hval : input.reals (s.nr 70 + (r + 1)) = 0
    · have g₂ : (Guard.real .eq 73 74).eval p = true := by simp [Guard.eval, realTest, p, hw, h0, hval]
      exact ⟨p, _, Run.seq he (Run.branchTrue g₁ (Run.branchTrue g₂ (Run.skip p))),
        by simpa [Pass, hval] using hflag, ha, h0, by decide⟩
    · have g₂ : (Guard.real .eq 73 74).eval p = false := by simp [Guard.eval, realTest, p, hw, h0, hval]
      exact ⟨_, _, Run.seq he (Run.branchTrue g₁ (Run.branchFalse g₂ (Run.atom reject p))),
        by simp [Pass, hbud, hval, reject, Atom.eval, Store.ofRAM, Store.at, ramStep], ha, h0, by decide⟩
  · have g₁ : (Guard.real .eq 72 74).eval p = false := by simp [Guard.eval, realTest, p, hb, h0, hbud]
    exact ⟨p, _, Run.seq he (Run.branchFalse g₁ (Run.skip p)),
      by simpa [Pass, hbud] using hflag, ha, h0, by decide⟩

theorem tests_run (input : RAMInput) (rs : List ℕ) (s : Store) (hz : s.rr 74 = 0) :
    ∃ t n, Run input (tests rs) s t n ∧
      t.nr 71 = (if ∀ r ∈ rs, Pass input (s.nr 70) r then s.nr 71 else 0) ∧ n ≤ 8 * rs.length := by
  classical
  induction rs generalizing s with
  | nil => exact ⟨s, 0, Run.skip s, by simp, by simp⟩
  | cons r rs ih =>
    obtain ⟨p, n, hp, hf, hb, h0, hn⟩ := test_run input r s hz
    obtain ⟨t, m, ht, hflag, hm⟩ := ih p h0
    rw [hb, hf] at hflag
    refine ⟨t, n + m, Run.seq hp ht, ?_, by simp only [List.length_cons]; omega⟩
    by_cases h1 : Pass input (s.nr 70) r <;> by_cases h2 : ∀ j ∈ rs, Pass input (s.nr 70) j <;>
      simpa [List.forall_mem_cons, h1, h2] using hflag

theorem input_passes {k : ℕ} (I : MultiInstance k) (ε : ℝ) (i : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[i]? = some e) :
    (∀ j ∈ List.range (k - 1), Pass (multiInput I ε) (InputValues.row k i) j) ↔
      ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0 := by
  have one (r : Fin (k - 1)) : Pass (multiInput I ε) (InputValues.row k i) r.val ↔
      (I.budget r = 0 → I.cost r e.1 e.2 = 0) := by
    simp only [Pass, InputValues.budget_read I ε r, InputValues.row_cost I ε i e he r, NNReal.coe_eq_zero]
  exact ⟨fun h r => (one r).mp (h r.val (List.mem_range.mpr r.isLt)), fun h j hj =>
    (one ⟨j, List.mem_range.mp hj⟩).mpr (h _)⟩

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

theorem tests_registers (rs : List ℕ) (a : ℕ) (h71 : a ≠ 71) (h72 : a ≠ 72) : a ∉ (tests rs).natWrites := by
  induction rs with
  | nil => simp [tests, Cmd.natWrites]
  | cons r rs ih =>
    have h : a ∉ (test r).natWrites := by
      simp [test, loadTest, reject, Cmd.atoms, Cmd.natWrites, Atom.natWrites, h71, h72]
    simpa [tests, Cmd.natWrites, h, ih]

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.RegisterShift
open Mission.Structured

theorem view_update {α : Type} (f : ℕ → α) (b x : ℕ) (v : α) :
    (fun j => Function.update f (b + x) v (b + j)) = Function.update (fun j => f (b + j)) x v := by
  funext j
  by_cases h : j = x
  · subst j; simp
  · simp [Function.update_of_ne h, Function.update_of_ne (show b + j ≠ b + x by omega)]

end NearLinearRSP.TwoResources.Supplement.RegisterShift

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

theorem copies_readonly (dst src n : ℕ) :
    (TableQuery.addCopies dst src n).writesNatMemory = false ∧
      (TableQuery.addCopies dst src n).writesRealMemory = false ∧ (TableQuery.addCopies dst src n).realWrites = ∅ := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih => simp [TableQuery.addCopies, Cmd.writesNatMemory, Cmd.writesRealMemory, Cmd.realWrites,
      Atom.writesNatMemory, Atom.writesRealMemory, Atom.realWrites, ih.1, ih.2.1, ih.2.2]

theorem tests_readonly (rs : List ℕ) : (tests rs).writesNatMemory = false ∧ (tests rs).writesRealMemory = false := by
  induction rs with
  | nil => exact ⟨rfl, rfl⟩
  | cons r rs ih =>
    change (false || (tests rs).writesNatMemory) = false ∧ (false || (tests rs).writesRealMemory) = false
    simpa using ih

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

def clockInput : List Atom := [⟨.natConst 65 0, trivial⟩, ⟨.loadNat 60 65, trivial⟩]
def clockOps : List Atom :=
  [⟨.realCopy 80 60, trivial⟩, ⟨.natConst 65 0, trivial⟩, ⟨.inputReal 81 65, trivial⟩, ⟨.realConst 84 8, trivial⟩,
   ⟨.realOp .div 81 81 84, trivial⟩, ⟨.realConst 84 1, trivial⟩, ⟨.realOp .add 81 84 81, trivial⟩,
   ⟨.loadReal 82 94, trivial⟩, ⟨.loadReal 83 65, trivial⟩, ⟨.realOp .sub 83 83 84, trivial⟩,
   ⟨.loadNat 79 94, trivial⟩, ⟨.natConst 74 0, trivial⟩, ⟨.realConst 74 0, trivial⟩, ⟨.natCopy 57 60, trivial⟩]
def clockCmd : Cmd := .seq (.atoms clockInput) (.seq Mission.NatToReal.convertCmd (.atoms clockOps))

theorem clocks_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (r : ℕ) (A : ClockCall k)
    (hcall : (outerCalls I ε)[r]? = some A) (s : Store) (h : CoordinateRAM.InputHeader I ε (s.at 0))
    (him : CallRAM.CallImage I ε s) (hptr : s.nr 94 = callBase I ε r) :
    ∃ t n, Run (multiInput I ε) clockCmd s t n ∧ Clocks A t ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      (∀ a, 94 ≤ a → t.nr a = s.nr a) ∧ n ≤ 14 * (Nat.log 2 A.q + 1) ^ 2 + 21 := by
  let input := multiInput I ε
  let p := evalAtoms input clockInput s
  obtain ⟨_, hδ, _⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? hcall)
  have hq : s.nm 0 = A.q := h.1.1.trans (by unfold multiQ ClockCall.q; rw [hδ])
  have hp : p.nr 60 = A.q := by simp [p, clockInput, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, hq]
  obtain ⟨v, c, he, hv, hc, hf⟩ := Mission.NatToReal.convertCmd_run input p
  have h60 : v.nr 60 = A.q := (hf.1 60 (by omega)).trans hp
  have hr60 : v.rr 60 = (A.q : ℝ) := hv.trans (by rw [hp])
  have vptr : v.nr 94 = callBase I ε r := (hf.1 94 (by omega)).trans hptr
  have vn : v.nm = s.nm := hf.2.2.1
  have vr : v.rm = s.rm := hf.2.2.2
  have hz : s.rm 0 = clockZ A := h.1.2.2.2.2.1.trans (by unfold clockZ; rw [hδ]; congr 2 <;> ring)
  have hden : (1 : ℝ) + ε / 8 = 1 + A.δ / 2 := by rw [hδ]; ring
  obtain ⟨htag, hL⟩ := him.bounds r A hcall
  have hin : input.reals 0 = ε := by simp [input, multiInput]
  let t := evalAtoms input clockOps v
  have run : Run input clockCmd s t (2 + (c + 14)) := Run.seq (run_atoms input clockInput s) (Run.seq he (run_atoms input clockOps v))
  refine ⟨t, _, run, ?_, vn, vr, ?_, ?_⟩
  · constructor <;> simp [t, clockOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, evalReal,
      hin, h60, hr60, vptr, vn, vr, hz, hden, htag, hL]
  · intro a ha
    have hother : t.nr a = v.nr a := by
      simp [t, clockOps, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_apply,
        show a ≠ 65 by omega, show a ≠ 79 by omega, show a ≠ 74 by omega, show a ≠ 57 by omega]
    have hprev : p.nr a = s.nr a := by
      simp [p, clockInput, evalAtoms, Atom.eval, Store.ofRAM, Store.at, ramStep, Function.update_apply,
        show a ≠ 65 by omega, show a ≠ 60 by omega]
    exact hother.trans ((hf.1 a (by omega)).trans hprev)
  · rw [hp] at hc; omega

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem Numbers.congr {k : ℕ} {A : ClockCall k} {base : ℕ} {T : MultiTable A.d} {s t : Store}
    (h : Numbers A base T s) (hf : ∀ x < extent A base, t.nm x = s.nm x ∧ t.rm x = s.rm x) :
    Numbers A base T t := by
  intro v hv j hj
  have he := row_end A base v j hv hj
  obtain ⟨hval, hrank⟩ := h v hv j hj
  exact ⟨((hf _ (by omega)).2).trans hval, ((hf _ (by omega)).1).trans hrank⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

theorem graph_transport {k : ℕ} (I : MultiInstance k) (map : ℕ) (s t : Store) (h : GraphRAM.Image I map s)
    (r141 : t.nr 141 = s.nr 141) (r142 : t.nr 142 = s.nr 142) (r143 : t.nr 143 = s.nr 143)
    (hf : ∀ x, map ≤ x → x < map + 3 * I.graph.n + I.graph.edges.length → t.nm x = s.nm x) :
    GraphRAM.Image I map t := by
  have hlen := h.vertices.length_le
  refine ⟨h.vertices.congr r141 r142 r143 (fun v hv => hf _ (by omega) (by omega)) (fun j hj => hf _ (by omega) (by omega)), ?_⟩
  intro v hv
  have hh := hf (map + 2 * I.graph.n + v) (by omega) (by change v < I.graph.n at hv; omega)
  rw [hh]
  apply (h.outgoing v hv).frame
  intro e he
  have hi := outgoingIndices_lt (lengthInstance I) I.graph.edges.length v e he
  apply hf _ (by omega) (by omega)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem TableImage.frame {k : ℕ} {A : ClockCall k} {base : ℕ} {T : MultiTable A.d} {s t : Store}
    (h : TableImage A base T s) (hf : ∀ x < extent A base, t.nm x = s.nm x ∧ t.rm x = s.rm x) :
    TableImage A base T t := ⟨h.numbers.congr hf, fun j hj => (h.parents j hj).congr hj hf⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

theorem shape_extra (k d : ℕ) (input : RAMInput) (s : Store) :
    let p := SpaceRAM.shaped k d input s
    p.nr 60 = s.nm 2 ∧ p.rr = s.rr ∧ ∀ a, 70 ≤ a → p.nr a = s.nr a := by
  dsimp only
  refine ⟨?_,rfl,?_⟩
  · simp [SpaceRAM.shaped,added,SpaceRAM.shapeOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep]
  · intro a ha
    simp [SpaceRAM.shaped,added,SpaceRAM.shapeOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,
      Function.update_of_ne (show a ≠ 49 by omega),Function.update_of_ne (show a ≠ 58 by omega),
      Function.update_of_ne (show a ≠ 31 by omega),Function.update_of_ne (show a ≠ 60 by omega),
      Function.update_of_ne (show a ≠ 57 by omega),Function.update_of_ne (show a ≠ 65 by omega),
      Function.update_of_ne (show a ≠ 30 by omega)]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

structure Hardware {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  header : CoordinateRAM.InputHeader I ε (s.at 0)
  calls : CallRAM.CallImage I ε s
  graph : GraphRAM.Image I (PrepareRAM.privateBase I ε) s
  cfg : Config (capacity I) (heapBase I ε) (parentsBase I ε) s
  keys : s.nr 189 = keyBase I ε
  params : s.nr 190 = paramBase I ε

theorem Hardware.copy {k : ℕ} {I : MultiInstance k} {ε : ℝ} {s t : Store} (h : Hardware I ε s)
    (nr : ∀ a, 100 ≤ a → a ≤ 190 → t.nr a = s.nr a) (nm : t.nm = s.nm) (rm : t.rm = s.rm) : Hardware I ε t := by
  have header : CoordinateRAM.InputHeader I ε (t.at 0) := by
    simpa only [CoordinateRAM.InputHeader,ScalarRAM.ScalarHeader,Store.at,nm,rm] using h.header
  have calls : CallRAM.CallImage I ε t := ⟨(congrFun nm _).trans h.calls.count,fun j A hj => by simpa only [nm,rm] using h.calls.bounds j A hj⟩
  exact ⟨header,calls,graph_transport I _ s t h.graph (nr 141 (by decide) (by decide)) (nr 142 (by decide) (by decide)) (nr 143 (by decide) (by decide))
    (fun _ _ _ => congrFun nm _),⟨(nr 180 (by decide) (by decide)).trans h.cfg.winnerBase,(nr 181 (by decide) (by decide)).trans h.cfg.parentBase,
    (nr 188 (by decide) (by decide)).trans h.cfg.capacity⟩,(nr 189 (by decide) (by decide)).trans h.keys,(nr 190 (by decide) (by decide)).trans h.params⟩

theorem call_monotone {k : ℕ} (I : MultiInstance k) (ε : ℝ) : Monotone (callBase I ε) :=
  (show StrictMono (callBase I ε) from fun _ _ h => PrepareRAM.call_increasing I ε h).monotone

theorem end_of_call {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (r : ℕ) (A : ClockCall k)
    (ha : (outerCalls I ε)[r]? = some A) : extent A (callBase I ε r) = callBase I ε (r+1) := by
  obtain ⟨hI,hδ,_⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? ha)
  simp only [extent,ClockCall.d,ClockCall.coords,ClockCall.q,callBase,multiQ,hI,hδ]
  ring

theorem site_of_call {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (r : ℕ) (A : ClockCall k)
    (ha : (outerCalls I ε)[r]? = some A) :
    Site A (callBase I ε r) (PrepareRAM.privateBase I ε) (paramBase I ε) (capacity I) (heapBase I ε) := by
  obtain ⟨hI,_,_⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? ha)
  have hb := PrepareRAM.call_lower I ε r
  have hlt := (List.getElem?_eq_some_iff.mp ha).1
  have dim : A.d ≤ k := clockCoordinates_length_le A.I
  refine ⟨by omega,?_,?_,?_,?_⟩
  · rw [end_of_call I ε hε r A ha]
    exact call_monotone I ε (show r+1 ≤ (outerCalls I ε).length by omega)
  · rw [hI]; unfold paramBase keyBase; omega
  · unfold heapBase; omega
  · rw [hI]; exact Nat.le_pow_clog (by decide) _

def PublicFrame {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : ℕ) (s t : Store) : Prop :=
  ∀ x < keyBase I ε, x < callBase I ε r + 4 ∨ callBase I ε (r+1) ≤ x → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem header_protected {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s t : Store)
    (h : CoordinateRAM.InputHeader I ε (s.at 0)) (hf : ∀ x < 8+k, t.nm x = s.nm x ∧ t.rm x = s.rm x) :
    CoordinateRAM.InputHeader I ε (t.at 0) := by
  obtain ⟨⟨hq,hs,hn,hk,hz,hH⟩,hd,hcoord⟩ := h
  refine ⟨⟨((hf 0 (by omega)).1).trans hq,((hf 1 (by omega)).1).trans hs,((hf 2 (by omega)).1).trans hn,
    ((hf 3 (by omega)).1).trans hk,((hf 0 (by omega)).2).trans hz,((hf 1 (by omega)).2).trans hH⟩,
    ((hf 4 (by omega)).1).trans hd,?_⟩
  intro j; have hh := j.isLt; have hk' := clockCoordinates_length_le I
  exact ((hf _ (by omega)).1).trans (hcoord j)

theorem PublicFrame.headers {k : ℕ} {I : MultiInstance k} {ε : ℝ} {r : ℕ} {s t : Store}
    (hf : PublicFrame I ε r s t) (h : Hardware I ε s) :
    CoordinateRAM.InputHeader I ε (t.at 0) ∧ CallRAM.CallImage I ε t := by
  have hb := PrepareRAM.call_lower I ε r
  have he : 32+2*k ≤ PrepareRAM.privateBase I ε := PrepareRAM.call_lower I ε _
  have hkey : PrepareRAM.privateBase I ε ≤ keyBase I ε := by unfold keyBase; omega
  have low (x : ℕ) (hx : x < 8+k) := hf x (by omega) (Or.inl (by omega))
  refine ⟨header_protected I ε s t h.header low,⟨((low 5 (by omega)).1).trans h.calls.count,?_⟩⟩
  intro j A hj
  have hlt := (List.getElem?_eq_some_iff.mp hj).1
  have hend : callBase I ε j < PrepareRAM.privateBase I ε := PrepareRAM.call_increasing I ε hlt
  have side : callBase I ε j < callBase I ε r + 4 ∨ callBase I ε (r+1) ≤ callBase I ε j := by
    rcases le_or_gt j r with hh | hh
    · have hl := call_monotone I ε hh; omega
    · exact Or.inr (call_monotone I ε (by omega))
  obtain ⟨hn,hr⟩ := hf _ (by omega) side
  obtain ⟨ht,hL⟩ := h.calls.bounds j A hj
  exact ⟨hn.trans ht,hr.trans hL⟩

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def thresholdAddress : Atom := ⟨.natCopy 94 200,trivial⟩
def oneCall (k : ℕ) := Cmd.seq (.atom thresholdAddress) (.seq EdgeRAM.clockCmd
  (.seq (.atoms dimensionOps) (selectDimension (buildTableCmd k) k)))

def oneCost (k d q B N m : ℕ) := tableCost k d q B N m + 14*(Nat.log 2 q+1)^2 + 2*k + 27

theorem build_call_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (r : ℕ) (A : ClockCall k)
    (ha : (outerCalls I ε)[r]? = some A) (s : Store) (h : Hardware I ε s) (baseReg : s.nr 200 = callBase I ε r)
    (blank : ∀ x, callBase I ε r+4 ≤ x → x < callBase I ε (r+1) → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput I ε) (oneCall k) s t n ∧ Hardware I ε t ∧
      TableImage A (callBase I ε r) (constructTable A) t ∧ PublicFrame I ε r s t ∧ t.nr 203 = callBase I ε (r+1) ∧
      t.nr 201 = s.nr 201 ∧ t.nr 202 = s.nr 202 ∧
      n ≤ oneCost k (clockCoordinates I).length (multiQ k ε) (capacity I) (incidentVertices I).length I.graph.edges.length := by
  obtain ⟨hI,hδ,hL⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? ha)
  subst I
  let I := A.I
  let base := callBase I ε r
  let input := multiInput I ε
  let p := thresholdAddress.eval input s
  have pnr (a : ℕ) (ha : 100 ≤ a) : p.nr a = s.nr a := Function.update_of_ne (by omega) _ _
  have ph : Hardware I ε p := h.copy (fun a ha _ => pnr a ha) rfl rfl
  obtain ⟨w,c,hr,clock,wn,wr,wreg,hc⟩ := EdgeRAM.clocks_run I ε hε r A ha p ph.header ph.calls baseReg
  let v := dimensioned w
  let b := marked v A.d
  have hmem : b.nm = s.nm := wn
  have hreal : b.rm = s.rm := wr
  have br (a : ℕ) (hb : 100 ≤ a) : b.nr a = s.nr a := by
    change Function.update (Function.update w.nr 68 (w.nm 4)) 69 A.d a = _
    rw [Function.update_of_ne (show a ≠ 69 by omega),Function.update_of_ne (show a ≠ 68 by omega)]
    exact (wreg _ (by omega)).trans (pnr _ hb)
  have bh : Hardware I ε b := h.copy (fun a hb _ => br a hb) hmem hreal
  have cq : A.q = multiQ k ε := by unfold ClockCall.q multiQ; rw [hδ]
  have hclocks : EdgeRAM.Clocks A b := ⟨clock.q,clock.zeroOnly,clock.zeroNat,clock.zeroReal,clock.limit,
    clock.denominator,clock.threshold,clock.decay⟩
  have inputB : TableInput A base (PrepareRAM.privateBase I ε) (keyBase I ε) (paramBase I ε) (capacity I)
      (heapBase I ε) (parentsBase I ε) b :=
    ⟨bh.cfg,bh.graph,hclocks,bh.header.2.2,bh.header.1.2.1,bh.header.1.2.2.1,bh.header.1.1.trans cq.symm,
      bh.keys,bh.params,(br _ (by decide)).trans baseReg⟩
  have hend : extent A base = callBase I ε (r+1) := end_of_call I ε hε r A ha
  have hb (x : ℕ) (hx : base+4 ≤ x) (he : x < extent A base) : b.nm x = 0 ∧ b.rm x = 0 := by
    rw [hmem,hreal]; exact blank x hx (he.trans_eq hend)
  have hpos : 0 < A.q := ticks_pos k A.δ hk (by rw [hδ]; positivity)
  obtain ⟨t,m,he,ct,table,frame,tend,preserve,hm⟩ := build_table_run A hk ε base (PrepareRAM.privateBase I ε) (keyBase I ε)
    (paramBase I ε) (height I) (heapBase I ε) (parentsBase I ε) (site_of_call I ε hε r A ha)
    le_rfl le_rfl le_rfl hpos (clockCoordinates_pos I hk) b inputB hb
  have dim : v.nr 68 = A.d := (congrFun wn 4).trans h.header.2.1
  obtain ⟨d,hsel,hd⟩ := select_dimension_run input (buildTableCmd k) k A.d (clockCoordinates_length_le I) v t m dim he
  have run : Run input (oneCall k) s t (1+(c+(2+d))) :=
    Run.seq (Run.atom thresholdAddress s) (Run.seq hr (Run.seq (dimension_run input w) hsel))
  have pub : PublicFrame I ε r s t := by
    intro x hx hh
    have side : x < base+4 ∨ extent A base ≤ x := by simpa only [hend,base] using hh
    have hf := frame x hx side
    exact ⟨hf.1.trans (congrFun hmem _),hf.2.trans (congrFun hreal _)⟩
  obtain ⟨th,tc⟩ := pub.headers h
  have keep (a : ℕ) (ha : 201 ≤ a) (hh : a ≤ 202) : t.nr a = s.nr a := by
    have ho : TableOuter k a := by
      unfold TableOuter; refine ⟨by omega,by unfold EdgeRAM.bank; omega,by omega,by omega,by omega,?_⟩
      intro j; unfold stateReg CandidateRAM.current; omega
    have hg : GridFixed a := by
      unfold GridFixed; refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
      intro j; unfold strideReg CandidateRAM.current; omega
    exact (preserve _ ho hg (by omega)).trans (br _ (by omega))
  refine ⟨t,_,run,⟨th,tc,ct.graph,ct.cfg,ct.keysReg,ct.paramsReg⟩,table,pub,tend.trans hend,
    keep 201 (by decide) (by decide),keep 202 (by decide) (by decide),?_⟩
  change m ≤ tableCost k A.d A.q (capacity I) (incidentVertices I).length I.graph.edges.length at hm
  unfold oneCost
  rw [← cq]
  change _ ≤ tableCost k A.d A.q (capacity I) (incidentVertices I).length I.graph.edges.length + _ + _ + _
  omega

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def Built {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : ℕ) (s : Store) : Prop :=
  ∀ j < r, ∀ A, (outerCalls I ε)[j]? = some A → TableImage A (callBase I ε j) (constructTable A) s
def Blank {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : ℕ) (s : Store) : Prop :=
  ∀ j, r ≤ j → j < (outerCalls I ε).length → ∀ x, callBase I ε j + 4 ≤ x → x < callBase I ε (j+1) → s.nm x = 0 ∧ s.rm x = 0
def TargetArea {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop :=
  ∀ x, 8+k ≤ x → x < callBase I ε 0 → s.nm x = 0 ∧ s.rm x = 0

structure OuterState {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : ℕ) (s : Store) : Prop where
  hardware : Hardware I ε s
  built : Built I ε r s
  blank : Blank I ε r s
  targets : TargetArea I ε s
  count : s.nr 201 = r
  total : s.nr 202 = (outerCalls I ε).length
  address : s.nr 200 = callBase I ε r

theorem call_interval {k : ℕ} (I : MultiInstance k) (ε : ℝ) (j x : ℕ) (hx : callBase I ε j+4 ≤ x)
    (hxr : x < callBase I ε (j+1)) : ∀ z, x ≠ callBase I ε z := by
  intro z
  rcases le_or_gt z j with h | h
  · have hz := call_monotone I ε h; omega
  · have hz := call_monotone I ε (show j+1 ≤ z by omega); omega

theorem prepared_blank {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (h : PrepareRAM.Prepared I ε s) :
    Blank I ε 0 s ∧ TargetArea I ε s := by
  have hb := PrepareRAM.call_lower I ε
  have privateBound := call_monotone I ε (Nat.zero_le (outerCalls I ε).length)
  change callBase I ε 0 ≤ PrepareRAM.privateBase I ε at privateBound
  constructor
  · intro j _ hj x hlo hhi
    have htop : callBase I ε (j+1) ≤ PrepareRAM.privateBase I ε := call_monotone I ε (by omega)
    have hl := hb j
    have free := call_interval I ε j x hlo hhi
    exact ⟨h.natZero x (by omega) (fun z _ => free z) (Or.inl (by omega)),h.realZero x (by omega) (fun z _ => free z)⟩
  · intro x hl hh
    have fr (z : ℕ) : x ≠ callBase I ε z := by have := call_monotone I ε (Nat.zero_le z); omega
    exact ⟨h.natZero x hl (fun z _ => fr z) (Or.inl (by omega)),h.realZero x (by omega) (fun z _ => fr z)⟩

def counterOps : List Atom :=
  [⟨.natCopy 200 49,trivial⟩,⟨.natConst 201 0,trivial⟩,⟨.natConst 65 5,trivial⟩,⟨.loadNat 202 65,trivial⟩]
def startCalls (k : ℕ) := Cmd.seq (SpaceRAM.shapeCmd k 0) (.atoms counterOps)

theorem start_calls_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (input : RAMInput) (s : Store)
    (h : Hardware I ε s) (empty : Blank I ε 0 s) (targets : TargetArea I ε s) :
    ∃ t, Run input (startCalls k) s t 23 ∧ OuterState I ε 0 t := by
  let p := SpaceRAM.shaped k 0 input s
  let t := evalAtoms input counterOps p
  obtain ⟨hr,_,_,hb,_,nm,rm⟩ := SpaceRAM.shape_run k 0 input s
  obtain ⟨_,_,reg⟩ := shape_extra k 0 input s
  have n : t.nm = s.nm := nm
  have r : t.rm = s.rm := rm
  have high (a : ℕ) (ha : 100 ≤ a) (hh : a ≤ 190) : t.nr a = s.nr a := by
    have hp := reg a (by omega)
    simpa [t,counterOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,
      Function.update_of_ne (show a ≠ 200 by omega),Function.update_of_ne (show a ≠ 201 by omega),
      Function.update_of_ne (show a ≠ 202 by omega),Function.update_of_ne (show a ≠ 65 by omega)] using hp
  have addr : p.nr 49 = callBase I ε 0 := by
    have nodes : s.nm 2 = I.graph.n := h.header.1.2.2.1
    rw [hb,nodes]; simp [callBase]
  refine ⟨t,Run.seq hr (run_atoms input counterOps p),⟨h.copy high n r,fun _ hj => (Nat.not_lt_zero _ hj).elim,
    fun j hj hh x hx hxr => ⟨(congrFun n _).trans (empty j hj hh x hx hxr).1,(congrFun r _).trans (empty j hj hh x hx hxr).2⟩,
    fun x hx hxr => ⟨(congrFun n _).trans (targets x hx hxr).1,(congrFun r _).trans (targets x hx hxr).2⟩,
    rfl,(congrFun nm 5).trans h.calls.count,addr⟩⟩

def nextCallOps : List Atom :=
  [⟨.natConst 65 1,trivial⟩,⟨.natOp .add 201 201 65,trivial⟩,⟨.natCopy 200 203,trivial⟩]
def callBody (k : ℕ) := Cmd.seq (oneCall k) (.atoms nextCallOps)
def callsLoop (k : ℕ) := Cmd.loop (.nat .lt 201 202) (callBody k)

theorem next_call_state {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (r : ℕ) (s : Store)
    (hh : r < (outerCalls I ε).length) (h : OuterState I ε r s) :
    ∃ t n, Run (multiInput I ε) (callBody k) s t n ∧ OuterState I ε (r+1) t ∧
      n ≤ oneCost k (clockCoordinates I).length (multiQ k ε) (capacity I) (incidentVertices I).length I.graph.edges.length + 3 := by
  let input := multiInput I ε
  let A := (outerCalls I ε)[r]
  have ha : (outerCalls I ε)[r]? = some A := List.getElem?_eq_getElem hh
  obtain ⟨p,c,hr,ph,im,frame,top,count,total,cost⟩ := build_call_run I hk ε hε r A ha s h.hardware h.address (h.blank r le_rfl hh)
  let t := evalAtoms input nextCallOps p
  have htop : callBase I ε (r+1) ≤ PrepareRAM.privateBase I ε := call_monotone I ε (by omega)
  have lim : PrepareRAM.privateBase I ε ≤ keyBase I ε := by unfold keyBase; omega
  have high (a : ℕ) (ha : 100 ≤ a) (hb : a ≤ 190) : t.nr a = p.nr a := by
    simp [t,nextCallOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Function.update_of_ne (show a ≠ 65 by omega),
      Function.update_of_ne (show a ≠ 200 by omega),Function.update_of_ne (show a ≠ 201 by omega)]
  have before := call_monotone I ε (Nat.zero_le r)
  refine ⟨t,c+3,Run.seq hr (run_atoms input nextCallOps p),⟨ph.copy high rfl rfl,?_,?_,?_,?_,total.trans h.total,top⟩,by omega⟩
  · intro j hj C hC
    by_cases eq : j = r
    · subst j
      have hAC : A = C := Option.some.inj (ha.symm.trans hC)
      subst C
      exact im.frame (fun _ _ => ⟨rfl,rfl⟩)
    · apply (h.built j (by omega) C hC).frame
      intro x hx
      rw [end_of_call I ε hε j C hC] at hx
      have le := call_monotone I ε (show j+1 ≤ r by omega)
      have early := call_monotone I ε (show r ≤ r+1 by omega)
      exact frame x (by omega) (Or.inl (by omega))
  · intro j hj hlen x hx hx'
    have early := call_monotone I ε hj
    have late : callBase I ε (j+1) ≤ PrepareRAM.privateBase I ε := call_monotone I ε (by omega)
    have hf := frame x (by omega) (Or.inr (by omega))
    have blank := h.blank j (by omega) hlen x hx hx'
    exact ⟨hf.1.trans blank.1,hf.2.trans blank.2⟩
  · intro x hx h0
    have early := call_monotone I ε (show r ≤ r+1 by omega)
    have hf := frame x (by omega) (Or.inl (by omega))
    have zero := h.targets x hx h0
    exact ⟨hf.1.trans zero.1,hf.2.trans zero.2⟩
  · simp [t,nextCallOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,count,h.count]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

noncomputable def unitWork {k : ℕ} (I : MultiInstance k) (ε : ℝ) :=
  oneCost k (clockCoordinates I).length (multiQ k ε) (capacity I) (incidentVertices I).length I.graph.edges.length + 5

theorem calls_loop_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    (remaining r : ℕ) (s : Store) (hend : r+remaining = (outerCalls I ε).length) (h : OuterState I ε r s) :
    ∃ t n, Run (multiInput I ε) (callsLoop k) s t n ∧ OuterState I ε (outerCalls I ε).length t ∧
      n ≤ unitWork I ε * remaining + 1 := by
  induction remaining generalizing r s with
  | zero =>
    rw [Nat.add_zero] at hend
    exact ⟨s,1,Run.loopFalse (by simp [Guard.eval,natTest,h.count,h.total,hend]),hend ▸ h,by simp⟩
  | succ l ih =>
    have hl : r < (outerCalls I ε).length := by omega
    have hg : (Guard.nat .lt 201 202).eval s = true := by simp [Guard.eval,natTest,h.count,h.total,hl]
    obtain ⟨p,c,hr,ph,hc⟩ := next_call_state I hk ε hε r s hl h
    obtain ⟨t,m,he,th,hm⟩ := ih (r+1) p (by omega) ph
    refine ⟨t,_,Run.loopTrue hg hr he,th,?_⟩
    rw [Nat.mul_succ]
    have hu : unitWork I ε = oneCost k (clockCoordinates I).length (multiQ k ε) (capacity I) (incidentVertices I).length I.graph.edges.length + 5 := rfl
    omega

def constructAll (k : ℕ) := Cmd.seq (PrepareRAM.cmd k) (.seq (arena k) (.seq (startCalls k) (callsLoop k)))

structure TableOutput {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  hardware : Hardware I ε s
  tables : Built I ε (outerCalls I ε).length s
  targets : TargetArea I ε s
  emptySpace : (outerCalls I ε).length = 0 → ∀ x, keyBase I ε ≤ x → s.nm x = 0 ∧ s.rm x = 0

theorem construct_all_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ t n, Run (multiInput I ε) (constructAll k) initialStore t n ∧ TableOutput I ε t ∧
      (n : ℝ) ≤ PrepareRAM.coefficient k * multiScale I ε +
        ((3*height I+41+unitWork I ε*(outerCalls I ε).length : ℕ) : ℝ) := by
  let input := multiInput I ε
  obtain ⟨s,n,hp,hprep,hc⟩ := PrepareRAM.prepare_bounded I hk ε hε hε1
  obtain ⟨v,b,hv,prep,cfg,keys,params,_,_,hb⟩ := arena_run I ε s hprep
  have hard : Hardware I ε v := ⟨prep.header,prep.calls,prep.graph,cfg,keys,params⟩
  obtain ⟨blank,targets⟩ := prepared_blank I ε v prep
  obtain ⟨w,hw,wh⟩ := start_calls_run I ε input v hard blank targets
  obtain ⟨t,c,hr,th,hl⟩ := calls_loop_run I hk ε hε (outerCalls I ε).length 0 w (by omega) wh
  have tail : b+(23+c) ≤ 3*height I+41+unitWork I ε*(outerCalls I ε).length := by omega
  have empty : (outerCalls I ε).length = 0 → ∀ x, keyBase I ε ≤ x → t.nm x = 0 ∧ t.rm x = 0 := by
    intro hz x hx
    have guard : (Guard.nat .lt 201 202).eval w = false := by simp [Guard.eval,natTest,wh.count,wh.total,hz]
    have hs : t = w := Mission.Queue.run_final_unique hr (Run.loopFalse guard)
    have wn : w.nm = v.nm := hw.natMemory_frame rfl
    have wr : w.rm = v.rm := hw.realMemory_frame rfl
    rw [hs,wn,wr]
    have hb := PrepareRAM.call_lower I ε (outerCalls I ε).length
    change 32+2*k ≤ PrepareRAM.privateBase I ε at hb
    unfold keyBase at hx
    exact ⟨prep.natZero x (by omega) (fun _ hh => by omega) (Or.inr hx),prep.realZero x (by omega) (fun _ hh => by omega)⟩
  refine ⟨t,n+(b+(23+c)),Run.seq hp (Run.seq hv (Run.seq hw hr)),⟨th.hardware,th.built,th.targets,empty⟩,?_⟩
  rw [Nat.cast_add]
  exact add_le_add hc (by exact_mod_cast tail)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM

def coarseWork (k w m h g : ℕ) : ℕ :=
  (2*(k*(4*g+5))+k+32 +
    (5+k*(4*g+4) + (15*(6*m) + (14*k+33+19*h+(k+19*h+39))*(3*m) +
      (9*k+32*k+w*g+19*h+65+6)*m + 17) + 2)*g) + 14*g^2+2*k+27+5

def workFactor (k : ℕ) := coarseWork k (25^(k+1)) 1 1 1

theorem coarse_work_bound (k w m h g : ℕ) (hm : 0 < m) (hh : 0 < h) (hg : 0 < g) :
    coarseWork k w m h g ≤ coarseWork k w 1 1 1 * m * h * g^2 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.ne'
  obtain ⟨g,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hg.ne'
  simp only [Nat.succ_eq_add_one]
  unfold coarseWork
  ring_nf
  omega

theorem capacity_le_twice {k : ℕ} (I : MultiInstance k) : capacity I ≤ 2*(incidentVertices I).length := by
  let n := (incidentVertices I).length
  have hn : 0 < n := List.length_pos_iff.mpr (List.ne_nil_of_mem (incident_source_mem I))
  change 2 ^ Nat.clog 2 n ≤ 2*n
  by_cases h1 : n = 1
  · simp [h1]
  · have hp : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) (by omega)
    have ht := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < n by omega)
    change 2^(Nat.clog 2 n-1) < n at ht
    have he : Nat.clog 2 n = (Nat.clog 2 n-1)+1 := by omega
    conv_lhs => rw [he,pow_succ]
    omega

theorem unit_bound {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) :
    unitWork I ε ≤ workFactor k * max 1 I.graph.edges.length * (Nat.clog 2 (2*capacity I)+1) * ((multiQ k ε+1)^k)^2 := by
  let q := multiQ k ε
  let d := (clockCoordinates I).length
  let m := I.graph.edges.length
  let N := (incidentVertices I).length
  let B := capacity I
  let M := max 1 m
  let H := Nat.clog 2 (2*B)+1
  let G := (q+1)^k
  have hm : m ≤ M := Nat.le_max_right _ _
  have hM : 0 < M := Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)
  have hN : N ≤ 3*M := by have hh := incident_length_bound I; change N ≤ 1+2*m at hh; omega
  have hB : B ≤ 6*M := by have hh : B ≤ 2*N := capacity_le_twice I; omega
  have hd : d ≤ k := clockCoordinates_length_le I
  have hD : (q+1)^d ≤ G := Nat.pow_le_pow_right (by omega) hd
  have hg : q^d ≤ G := (Nat.pow_le_pow_left (Nat.le_succ q) d).trans hD
  have hq : q+1 ≤ G := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<q+1) (show 1≤k by omega)
  have hlog : Nat.log 2 q+1 ≤ G := by have hh := Nat.log_le_self 2 q; omega
  have hw : 25^(d+1) ≤ 25^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hh : Nat.clog 2 (2*B) ≤ H := Nat.le_succ _
  change oneCost k d q B N m + 5 ≤ workFactor k * M * H * G^2
  calc
    _ ≤ coarseWork k (25^(k+1)) M H G := by
      unfold oneCost tableCost stepCost layerWork visitCost vertexCost coarseWork
      gcongr <;> first | assumption | omega
    _ ≤ _ := coarse_work_bound k _ M H G hM (by unfold H; omega) (by omega)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured

noncomputable def heightFactor : ℝ := 3 + 1 / Real.log 2

theorem height_factor_pos : 0 < heightFactor := by unfold heightFactor; positivity

theorem tournament_depth {k : ℕ} (I : MultiInstance k) : Nat.clog 2 (2*capacity I) + 1 = height I + 2 := by
  unfold capacity
  rw [← pow_succ',Nat.clog_pow _ _ (by decide)]

theorem depth_bound {k : ℕ} (I : MultiInstance k) :
    ((Nat.clog 2 (2*capacity I) + 1 : ℕ) : ℝ) ≤ heightFactor * (1 + Real.log (max 2 I.graph.n : ℕ)) := by
  let V := (incidentVertices I).length
  let N : ℝ := (max 2 I.graph.n : ℕ)
  have hv : 0 < V := List.length_pos_iff.mpr (List.ne_nil_of_mem (incident_source_mem I))
  have h1 : (1:ℝ) ≤ V := by exact_mod_cast hv
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hVN : (V:ℝ) ≤ N := by
    have hh : V ≤ I.graph.n := ParentQuery.incident_length_le_n I
    dsimp [N]; exact_mod_cast hh.trans (Nat.le_max_right 2 I.graph.n)
  have log2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have logN := Real.log_nonneg hN
  have hh : (height I : ℝ) < Real.logb 2 (V:ℝ) + 1 := by
    change (Nat.clog 2 V : ℝ) < _
    rw [← Real.natCeil_logb_natCast]
    exact Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) h1)
  have hcmp : Real.logb 2 (V:ℝ) ≤ Real.log N / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hVN) log2.le
  have inv : 0 < (1:ℝ)/Real.log 2 := by positivity
  rw [tournament_depth]
  change ((height I + 2 : ℕ) : ℝ) ≤ heightFactor * (1 + Real.log N)
  push_cast
  unfold heightFactor
  rw [div_eq_mul_inv] at hcmp
  simp only [one_div] at inv ⊢
  nlinarith only [hh,hcmp,logN,inv]

noncomputable def gridFactor (k : ℕ) : ℝ := (workFactor k : ℝ) * heightFactor * (12*(8192*(k:ℝ)+2)^(2*k))
noncomputable def tableCoefficient (k : ℕ) := PrepareRAM.coefficient k + 3*heightFactor + 41 + gridFactor k

theorem calls_work_bound {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((unitWork I ε : ℝ) * (outerCalls I ε).length) ≤ gridFactor k * multiScale I ε := by
  let M : ℝ := (max 1 I.graph.edges.length : ℕ)
  let H := 1 + Real.log (max 2 I.graph.n : ℕ)
  let G : ℝ := (multiQ k ε + 1 : ℕ)
  let C : ℝ := (outerCalls I ε).length
  let W : ℝ := workFactor k
  let D : ℝ := (Nat.clog 2 (2 * capacity I)+1 : ℕ)
  have u : (unitWork I ε : ℝ) ≤ W*M*D*(G^k)^2 := by
    dsimp only [W,M,D,G]
    exact_mod_cast unit_bound I hk ε
  have hD : D ≤ heightFactor * H := depth_bound I
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hsc := scaled_grid_work_bound I ε hε hε1
  have hp : (G^k)^2 = G^(2*k) := by rw [← pow_mul,Nat.mul_comm]
  change _ ≤ gridFactor k * multiScale I ε
  calc
    _ ≤ W*M*D*(G^k)^2*C := mul_le_mul_of_nonneg_right u hC
    _ ≤ W*M*(heightFactor*H)*(G^k)^2*C := by gcongr
    _ = (W*heightFactor)*(M*H*(C*G^(2*k))) := by rw [hp]; ring
    _ ≤ (W*heightFactor)*((12*(8192*(k:ℝ)+2)^(2*k))*multiScale I ε) :=
      mul_le_mul_of_nonneg_left hsc (mul_nonneg hW height_factor_pos.le)
    _ = _ := by unfold gridFactor W; ring

theorem construct_all_bound {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ t n, Run (multiInput I ε) (constructAll k) initialStore t n ∧ TableOutput I ε t ∧
      (n : ℝ) ≤ tableCoefficient k * multiScale I ε := by
  obtain ⟨t,n,hr,h,hn⟩ := construct_all_run I hk ε hε hε1
  have one := SpaceRAM.scale_one I hk ε hε hε1
  let H := 1+Real.log (max 2 I.graph.n : ℕ)
  have logN := Real.log_nonneg (show (1:ℝ) ≤ (max 2 I.graph.n : ℕ) by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega))
  have hs : H^2 ≤ multiScale I ε := (PrepareRAM.graph_scales I ε hε hε1).2
  have h1 : 1 ≤ H := by dsimp [H]; linarith
  have hH : H ≤ multiScale I ε := (show H ≤ H^2 by nlinarith only [h1,sq_nonneg (H-1)]).trans hs
  have d := depth_bound I
  rw [tournament_depth] at d
  simp only [Nat.cast_add,Nat.cast_ofNat] at d
  have dh : (height I : ℝ) ≤ heightFactor*H := by change _ ≤ heightFactor*H at d; linarith
  have dh' := dh.trans (mul_le_mul_of_nonneg_left hH height_factor_pos.le)
  have cg := calls_work_bound I hk ε hε hε1
  push_cast at hn
  refine ⟨t,n,hr,h,?_⟩
  unfold tableCoefficient
  linarith only [hn,dh',one,cg]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

noncomputable def acceptsIndex {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v r : ℕ) : Bool :=
  match (outerCalls I ε)[r]? with
  | none => false
  | some A => accepts A v

noncomputable def displacement {k : ℕ} (I : MultiInstance k) (v : ℕ) := 4 + ((clockCoordinates I).length+4)*v

structure Inputs {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (s : Store) : Prop where
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  endReg : s.nr 202 = (outerCalls I ε).length
  width : s.nr 207 = CallRAM.callWidth I ε
  cutoff : s.rr 89 = 3/4
  factor : s.rr 91 = 1+ε/4
  headers : CallRAM.CallImage I ε s
  tables : Built I ε (outerCalls I ε).length s

def Answer {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Option ℕ → Prop
  | none => s.nr 210 = 0
  | some r => s.nr 210 = 3 ∧ s.nr 211 = callBase I ε r ∧ ∀ A, (outerCalls I ε)[r]? = some A → s.rr 90 = callReported ε A

theorem acceptance_read {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (r v : ℕ)
    (A : ClockCall k) (ha : (outerCalls I ε)[r]? = some A) (hv : v ∈ incidentVertices I) (s : Store)
    (im : TableImage A (callBase I ε r) (constructTable A) s) :
    s.rm (callBase I ε r + displacement I v) < 3/4 ↔ acceptsIndex I ε v r = false := by
  obtain ⟨hI,hδ,_⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? ha)
  subst I
  let j : Fin A.d → ℕ := fun _ => 0
  have hq : 0 < A.q := ticks_pos k A.δ hk (by rw [hδ]; positivity)
  have hd := (im.numbers v hv j (fun _ => hq)).1
  have addr : rowCell A (callBase A.I ε r) j v = callBase A.I ε r + displacement A.I v := by
    simp [rowCell,scanAddress,j,vectorIndex,displacement,ClockCall.d,ClockCall.coords,Nat.add_assoc]
  rw [addr] at hd
  rw [hd]
  simp only [acceptsIndex,ha,accepts,decide_eq_false_iff_not,not_le]
  rw [value_of_valid A _ v _ (fun _ => hq)]
  change 1-(constructTable A v j).value < 3/4 ↔ 1/4 < (constructTable A v j).value
  constructor <;> intro h <;> linarith

def selectLoad : Atom := ⟨.loadReal 88 206,trivial⟩
def missOps : List Atom :=
  [⟨.natOp .add 204 204 31,trivial⟩,⟨.natOp .add 205 205 207,trivial⟩,⟨.natOp .add 206 206 207,trivial⟩]
def hitOps : List Atom :=
  [⟨.natConst 210 3,trivial⟩,⟨.natCopy 211 205,trivial⟩,⟨.loadNat 213 205,trivial⟩,
   ⟨.loadReal 90 205,trivial⟩,⟨.natCopy 204 202,trivial⟩]
def hitCmd := Cmd.seq (.atoms hitOps) (.branch (.nat .eq 213 30)
  (.atom ⟨.realOp .mul 90 91 90,trivial⟩) (.atom ⟨.realConst 90 0,trivial⟩))
def selectBody := Cmd.seq (.atom selectLoad) (.branch (.real .lt 88 89) (.atoms missOps) hitCmd)
def selectLoop := Cmd.loop (.nat .lt 204 202) selectBody

theorem hit_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v r : ℕ) (A : ClockCall k)
    (ha : (outerCalls I ε)[r]? = some A) (input : RAMInput) (s : Store) (h : Inputs I ε v s) (hb : s.nr 205 = callBase I ε r) :
    ∃ t n, Run input hitCmd s t n ∧ Answer I ε t (some r) ∧ t.nr 204 = t.nr 202 ∧ n ≤ 8 := by
  let p := evalAtoms input hitOps s
  obtain ⟨tag,H⟩ := h.headers.bounds r A ha
  have hp : p.nr 210 = 3 ∧ p.nr 211 = callBase I ε r ∧ p.nr 213 = (if A.zeroOnly then 1 else 0) ∧
      p.rr 90 = A.L ∧ p.nr 204 = p.nr 202 := by
    simp [p,hitOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,hb,tag,H]
  obtain ⟨val,addr,mode,thresh,doneReg⟩ := hp
  have zero : p.nr 30 = 0 := h.zero
  have factor : p.rr 91 = 1+ε/4 := h.factor
  by_cases hz : A.zeroOnly = true
  · let a : Atom := ⟨.realConst 90 0,trivial⟩
    have guard : (Guard.nat .eq 213 30).eval p = false := by simp [Guard.eval,natTest,mode,hz,zero]
    refine ⟨_,_,Run.seq (run_atoms input hitOps s) (Run.branchFalse guard (Run.atom a p)),⟨val,addr,?_⟩,doneReg,by decide⟩
    intro C hC
    obtain rfl := Option.some.inj (ha.symm.trans hC)
    simp [a,Atom.eval,Store.ofRAM,Store.at,ramStep,callReported,hz]
  · let a : Atom := ⟨.realOp .mul 90 91 90,trivial⟩
    have guard : (Guard.nat .eq 213 30).eval p = true := by simp [Guard.eval,natTest,mode,hz,zero]
    refine ⟨_,_,Run.seq (run_atoms input hitOps s) (Run.branchTrue guard (Run.atom a p)),⟨val,addr,?_⟩,doneReg,by decide⟩
    intro C hC
    obtain rfl := Option.some.inj (ha.symm.trans hC)
    simp [a,Atom.eval,Store.ofRAM,Store.at,ramStep,evalReal,thresh,factor,callReported,hz]

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

theorem Inputs.copy {k : ℕ} {I : MultiInstance k} {ε : ℝ} {v : ℕ} {s t : Store} (h : Inputs I ε v s)
    (nr : ∀ a, a ∈ [30,31,202,207] → t.nr a = s.nr a) (rr : ∀ a, a = 89 ∨ a = 91 → t.rr a = s.rr a)
    (nm : t.nm = s.nm) (rm : t.rm = s.rm) : Inputs I ε v t :=
  ⟨(nr _ (by decide)).trans h.zero,(nr _ (by decide)).trans h.one,(nr _ (by decide)).trans h.endReg,
    (nr _ (by decide)).trans h.width,(rr _ (Or.inl rfl)).trans h.cutoff,(rr _ (Or.inr rfl)).trans h.factor,
    ⟨(congrFun nm _).trans h.headers.count, fun j A hj => by simpa only [nm,rm] using h.headers.bounds j A hj⟩,
    fun j hj A ha => (h.tables j hj A ha).frame (fun _ _ => ⟨congrFun nm _,congrFun rm _⟩)⟩

theorem first_accept_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (v : ℕ)
    (hv : v ∈ incidentVertices I) (input : RAMInput) (remaining j : ℕ) (s : Store)
    (hend : j+remaining = (outerCalls I ε).length) (h : Inputs I ε v s) (idx : s.nr 204 = j)
    (base : s.nr 205 = callBase I ε j) (cell : s.nr 206 = callBase I ε j + displacement I v) (blank : s.nr 210 = 0) :
    ∃ t n, Run input selectLoop s t n ∧ Answer I ε t ((List.range' j remaining).find? (acceptsIndex I ε v)) ∧
      n ≤ 13 * remaining + 1 := by
  induction remaining generalizing j s with
  | zero =>
    have g : (Guard.nat .lt 204 202).eval s = false := by simp [Guard.eval,natTest,idx,h.endReg,← hend]
    exact ⟨s,1,Run.loopFalse g,blank,by omega⟩
  | succ m ih =>
    have hl : j < (outerCalls I ε).length := by omega
    let A := (outerCalls I ε)[j]
    have ha : (outerCalls I ε)[j]? = some A := List.getElem?_eq_getElem hl
    have test := acceptance_read I hk ε hε j v A ha hv s (h.tables j hl A ha)
    have g : (Guard.nat .lt 204 202).eval s = true := by simp [Guard.eval,natTest,idx,h.endReg,hl]
    let p := selectLoad.eval input s
    have ph : Inputs I ε v p := h.copy (fun _ _ => rfl) (fun a hh =>
      Function.update_of_ne (show a ≠ 88 by omega) _ _) rfl rfl
    have pval : p.rr 88 = s.rm (callBase I ε j + displacement I v) := congrArg s.rm cell
    cases acc : acceptsIndex I ε v j with
    | false =>
      have less := test.mpr acc
      have gf : (Guard.real .lt 88 89).eval p = true := by simp [Guard.eval,realTest,pval,ph.cutoff,less]
      let w := evalAtoms input missOps p
      have wrun : Run input (.atoms missOps) p w 3 := run_atoms input missOps p
      have wh : Inputs I ε v w := ph.copy (fun a ha => wrun.nat_frame a (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        simp [missOps,Cmd.atoms,Cmd.natWrites,Atom.natWrites];omega)) (fun _ _ => rfl) rfl rfl
      have next : callBase I ε (j+1) = callBase I ε j + CallRAM.callWidth I ε := by
        rw [CallRAM.address_width I ε (j+1),CallRAM.address_width I ε j,Nat.mul_succ]; omega
      have ip : p.nr 204 = j := idx
      have bp : p.nr 205 = callBase I ε j := base
      have cp : p.nr 206 = callBase I ε j + displacement I v := cell
      have fields : w.nr 204 = j+1 ∧ w.nr 205 = callBase I ε (j+1) ∧ w.nr 206 = callBase I ε (j+1)+displacement I v := by
        simp [w,missOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,ip,bp,cp,ph.one,ph.width,next]
        omega
      obtain ⟨t,c,hr,ans,hc⟩ := ih (j+1) w (by omega) wh fields.1 fields.2.1 fields.2.2 blank
      simp only [List.range'_succ,List.find?_cons,acc,Bool.false_eq_true,if_false]
      exact ⟨t,_,Run.loopTrue g (Run.seq (Run.atom selectLoad s) (Run.branchTrue gf wrun)) hr,ans,by omega⟩
    | true =>
      have greater : ¬s.rm (callBase I ε j + displacement I v) < 3/4 := by
        intro hh
        have eq := test.mp hh
        simp [acc] at eq
      have gf : (Guard.real .lt 88 89).eval p = false := by simp [Guard.eval,realTest,pval,ph.cutoff,greater]
      obtain ⟨t,c,hr,ans,stop,hc⟩ := hit_run I ε v j A ha input p ph base
      have exitG : (Guard.nat .lt 204 202).eval t = false := by simp [Guard.eval,natTest,stop]
      simp only [List.range'_succ,List.find?_cons,acc,if_true]
      exact ⟨t,_,Run.loopTrue g (Run.seq (Run.atom selectLoad s) (Run.branchFalse gf hr)) (Run.loopFalse exitG),ans,by omega⟩

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

def Result {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (s : Store) : Prop :=
  s.nr 210 = outputTag (selectedBranch I ε v) ∧ (∀ d, selectedDistance I ε v = some d → s.rr 90 = d) ∧
    ∀ r, selectedBranch I ε v = .table r → s.nr 211 = callBase I ε r

theorem first_result {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (s : Store) (hv : v ≠ I.source)
    (pos : hasPositiveBudget I = true)
    (h : Answer I ε s ((List.range (outerCalls I ε).length).find? (acceptsIndex I ε v))) : Result I ε v s := by
  have branch : selectedBranch I ε v = match (List.range (outerCalls I ε).length).find? (acceptsIndex I ε v) with
      | none => .absent | some r => .table r := by simp only [selectedBranch,if_neg hv,pos,if_true]; rfl
  cases eq : (List.range (outerCalls I ε).length).find? (acceptsIndex I ε v) with
  | none =>
    rw [eq] at h branch
    exact ⟨by simpa [branch,outputTag,Answer] using h,fun d hd => by simp [selectedDistance,branch] at hd,fun r hr => by simp [branch] at hr⟩
  | some r =>
    rw [eq] at h branch
    obtain ⟨ht,ha,hd⟩ := h
    refine ⟨by simpa [branch,outputTag] using ht,?_,?_⟩
    · intro d hv
      cases hc : (outerCalls I ε)[r]? with
      | none => simp [selectedDistance,branch,hc] at hv
      | some A =>
        have eqd : callReported ε A = d := by simpa [selectedDistance,branch,hc,callReported] using hv
        exact (hd A hc).trans eqd
    · intro j hj
      have eqj : r = j := by simpa [branch] using hj
      simpa only [← eqj] using ha

def sourceTag : Atom := ⟨.natConst 210 1,trivial⟩
def selectTarget := Cmd.branch (.nat .eq 212 209) (.atom sourceTag) selectLoop

theorem select_target_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (pos : hasPositiveBudget I = true)
    (v : ℕ) (hv : v ∈ incidentVertices I) (input : RAMInput) (s : Store) (h : Inputs I ε v s)
    (idx : s.nr 204 = 0) (base : s.nr 205 = callBase I ε 0) (cell : s.nr 206 = callBase I ε 0 + displacement I v)
    (blank : s.nr 210 = 0) (tgt : s.nr 212 = v) (src : s.nr 209 = I.source) (real0 : s.rr 90 = 0) :
    ∃ t n, Run input selectTarget s t n ∧ Result I ε v t ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      n ≤ 13*(outerCalls I ε).length+3 := by
  by_cases hs : v = I.source
  · have g : (Guard.nat .eq 212 209).eval s = true := by simp [Guard.eval,natTest,tgt,src,hs]
    refine ⟨_,3,Run.branchTrue g (Run.atom sourceTag s),⟨?_,?_,?_⟩,rfl,rfl,by omega⟩
    · simp [selectedBranch,hs,sourceTag,Atom.eval,Store.ofRAM,Store.at,ramStep,outputTag]
    · intro d hd; simp [selectedDistance,selectedBranch,hs] at hd
      exact real0.trans hd
    · intro r hr; simp [selectedBranch,hs] at hr
  · have g : (Guard.nat .eq 212 209).eval s = false := by simp [Guard.eval,natTest,tgt,src,hs]
    obtain ⟨t,n,hr,ans,hc⟩ := first_accept_run I hk ε hε v hv input (outerCalls I ε).length 0 s (by omega) h idx base cell blank
    have hr' : Run input selectTarget s t (1+n) := Run.branchFalse g hr
    have ans' : Answer I ε t ((List.range (outerCalls I ε).length).find? (acceptsIndex I ε v)) := by
      simpa only [List.range_eq_range'] using ans
    exact ⟨t,_,hr',first_result I ε v t hs pos ans',hr.natMemory_frame rfl,hr.realMemory_frame rfl,by omega⟩

def selectFinish : List Atom :=
  [⟨.storeNat 214 210,trivial⟩,⟨.storeReal 214 90,trivial⟩,⟨.natOp .add 86 214 31,trivial⟩,
   ⟨.storeNat 86 211,trivial⟩,⟨.natOp .add 208 208 31,trivial⟩]

def TargetRecord {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (s : Store) : Prop :=
  s.nm (targetSlot k v) = outputTag (selectedBranch I ε v) ∧
    (∀ d, selectedDistance I ε v = some d → s.rm (targetSlot k v) = d) ∧
    ∀ r, selectedBranch I ε v = .table r → s.nm (targetSlot k v+1) = callBase I ε r

theorem finish_target {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (input : RAMInput) (s : Store)
    (h : Result I ε v s) (src : s.nr 214 = targetSlot k v) (one : s.nr 31 = 1) :
    let t := evalAtoms input selectFinish s
    TargetRecord I ε v t ∧ t.nr 208 = s.nr 208 + 1 ∧
      (∀ x, x ≠ targetSlot k v → x ≠ targetSlot k v+1 → t.nm x = s.nm x) ∧
      (∀ x, x ≠ targetSlot k v → t.rm x = s.rm x) := by
  let a := targetSlot k v
  let t := evalAtoms input selectFinish s
  have natM : t.nm = Function.update (Function.update s.nm a (s.nr 210)) (a+1) (s.nr 211) := by
    simp [t,a,selectFinish,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,src,one]
  have realM : t.rm = Function.update s.rm a (s.rr 90) := by
    simp [t,a,selectFinish,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,src]
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · change t.nm a = _
    simpa only [natM,Function.update_of_ne (show a ≠ a+1 by omega),Function.update_self] using h.1
  · intro d hd
    change t.rm a = _
    simpa only [realM,Function.update_self] using h.2.1 d hd
  · intro r hr
    change t.nm (a+1) = _
    simpa only [natM,Function.update_self] using h.2.2 r hr
  · simp [selectFinish,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,one]
  · intro x h0 h1; change t.nm x = s.nm x
    rw [natM]; change x ≠ a at h0; change x ≠ a+1 at h1
    rw [Function.update_of_ne h1,Function.update_of_ne h0]
  · intro x h0; change t.rm x = s.rm x
    rw [realM]; change x ≠ a at h0; rw [Function.update_of_ne h0]

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

def vertexOps (k : ℕ) : List Atom :=
  [⟨.natOp .add 86 34 208,trivial⟩,⟨.loadNat 212 86,trivial⟩,⟨.natOp .add 86 212 212,trivial⟩,
   ⟨.natOp .add 86 86 86,trivial⟩,⟨.natConst 214 (32+2*k),trivial⟩,⟨.natOp .add 214 214 86,trivial⟩,
   ⟨.natConst 204 0,trivial⟩,⟨.natCopy 205 200,trivial⟩,⟨.natConst 206 4,trivial⟩,
   ⟨.natOp .add 206 205 206,trivial⟩,⟨.natConst 210 0,trivial⟩,⟨.natConst 211 0,trivial⟩,⟨.realConst 90 0,trivial⟩]

def positiveVertex (k d : ℕ) := Cmd.seq (.atoms (vertexOps k))
  (.seq (addCopies 206 212 (d+4)) (.seq selectTarget (.atoms selectFinish)))

def FixedNat (a : ℕ) := a ∈ [30,31,34,35,200,202,207,209]
def FixedReal (a : ℕ) := a = 89 ∨ a = 91

theorem vertex_registers (k d a : ℕ) (ha : FixedNat a) : a ∉ (positiveVertex k d).natWrites := by
  have copies := copies_preserve 206 212 (d+4) a (by simp [FixedNat] at ha; omega)
  have target : ∀ i ∈ selectTarget.natWrites, i ∈ [204,205,206,210,211,213] := by decide
  have nt : a ∉ selectTarget.natWrites := by
    intro h
    have hh := target a h
    simp [FixedNat] at ha; simp at hh; omega
  simp [positiveVertex,vertexOps,selectFinish,Cmd.atoms,Cmd.natWrites,Atom.natWrites,copies,nt]
  simp [FixedNat] at ha; omega

theorem vertex_reals (k d a : ℕ) (ha : FixedReal a) : a ∉ (positiveVertex k d).realWrites := by
  have copies := (EdgeRAM.copies_readonly 206 212 (d+4)).2.2
  have target : ∀ i ∈ selectTarget.realWrites, i ∈ [88,90] := by decide
  have nt : a ∉ selectTarget.realWrites := by
    intro h
    have hh := target a h
    simp at hh; rcases ha with h|h <;> omega
  simp [positiveVertex,vertexOps,selectFinish,Cmd.atoms,Cmd.realWrites,Atom.realWrites,copies,nt]
  rcases ha with h|h <;> omega

theorem positive_vertex_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    (pos : hasPositiveBudget I = true) (v : ℕ) (hv : v ∈ incidentVertices I) (input : RAMInput) (s : Store)
    (h : Inputs I ε v s) (read : s.nm (s.nr 34 + s.nr 208) = v)
    (start : s.nr 200 = callBase I ε 0) (src : s.nr 209 = I.source) :
    ∃ t n, Run input (positiveVertex k (clockCoordinates I).length) s t n ∧ TargetRecord I ε v t ∧
      t.nr 208 = s.nr 208 + 1 ∧
      (∀ x, x ≠ targetSlot k v → x ≠ targetSlot k v+1 → t.nm x = s.nm x) ∧
      (∀ x, x ≠ targetSlot k v → t.rm x = s.rm x) ∧ n ≤ (clockCoordinates I).length + 13*(outerCalls I ε).length + 25 := by
  let d := (clockCoordinates I).length
  let p := evalAtoms input (vertexOps k) s
  let w := added 206 212 (d+4) p
  have hp : Run input (.atoms (vertexOps k)) s p 13 := run_atoms input _ _
  have hw : Run input (addCopies 206 212 (d+4)) p w (d+4) := add_copies_run input _ _ (by decide) _ _
  have pv : p.nr 212 = v ∧ p.nr 214 = targetSlot k v ∧ p.nr 205 = callBase I ε 0 ∧
      p.nr 206 = callBase I ε 0 + 4 := by
    simp [p,vertexOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,read,start,targetSlot]; omega
  have wh : Inputs I ε v w := h.copy (fun a hmem => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl <;> rfl) (fun a hh => by rcases hh with rfl|rfl <;> rfl) rfl rfl
  have wcell : w.nr 206 = callBase I ε 0 + displacement I v := by
    simp [w,added,pv.1,pv.2.2.2,displacement,d,Nat.add_assoc]
  obtain ⟨u,c,hu,res,un,ur,hc⟩ := select_target_run I hk ε hε pos v hv input w wh rfl pv.2.2.1 wcell rfl pv.1 src rfl
  have fa := finish_target I ε v input u res ((hu.nat_frame 214 (by decide)).trans pv.2.1)
    ((hu.nat_frame 31 (by decide)).trans wh.one)
  have ne : u.nr 208 = s.nr 208 := hu.nat_frame 208 (by decide)
  refine ⟨_,_,Run.seq hp (Run.seq hw (Run.seq hu (run_atoms input selectFinish u))),fa.1,?_,?_,?_,?_⟩
  · rw [fa.2.1,ne]
  · intro x h0 h1; exact (fa.2.2.1 x h0 h1).trans (congrFun un x)
  · intro x h0; exact (fa.2.2.2 x h0).trans (congrFun ur x)
  · change 13+(d+4+(c+5)) ≤ d+13*(outerCalls I ε).length+25; omega

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

structure Objects {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  header : CoordinateRAM.InputHeader I ε (s.at 0)
  calls : CallRAM.CallImage I ε s
  tables : Built I ε (outerCalls I ε).length s
  active : ∀ j v, (incidentVertices I)[j]? = some v → s.nm (PrepareRAM.privateBase I ε + I.graph.n + j) = v

def Outside {k : ℕ} (I : MultiInstance k) (s t : Store) : Prop :=
  ∀ x, x < targetSlot k 0 ∨ targetSlot k I.graph.n ≤ x → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem slot_before_call {k : ℕ} (I : MultiInstance k) (ε : ℝ) (r : ℕ) :
    targetSlot k I.graph.n ≤ callBase I ε r := by unfold targetSlot callBase; omega

theorem target_frame {k : ℕ} (I : MultiInstance k) (v : ℕ) (hv : v < I.graph.n) (s t : Store)
    (hn : ∀ x, x ≠ targetSlot k v → x ≠ targetSlot k v+1 → t.nm x = s.nm x)
    (hr : ∀ x, x ≠ targetSlot k v → t.rm x = s.rm x) : Outside I s t := by
  intro x hx
  have h0 : x ≠ targetSlot k v := by unfold targetSlot at *; omega
  have h1 : x ≠ targetSlot k v+1 := by unfold targetSlot at *; omega
  exact ⟨hn x h0 h1,hr x h0⟩

theorem Objects.frame {k : ℕ} {I : MultiInstance k} {ε : ℝ} {s t : Store} (h : Objects I ε s)
    (f : Outside I s t) : Objects I ε t := by
  have low (x : ℕ) (hx : x < 8+k) := f x (Or.inl (by unfold targetSlot; omega))
  refine ⟨header_protected I ε s t h.header low,⟨((low 5 (by omega)).1).trans h.calls.count,?_⟩,?_,?_⟩
  · intro r A ha
    have ff := f _ (Or.inr (slot_before_call I ε r))
    obtain ⟨ht,hL⟩ := h.calls.bounds r A ha
    exact ⟨ff.1.trans ht,ff.2.trans hL⟩
  · intro r hr A ha
    let base := callBase I ε r
    have b : targetSlot k I.graph.n ≤ base := slot_before_call I ε r
    have im := h.tables r hr A ha
    have high (i : Fin A.d → ℕ) (v off : ℕ) := f (rowCell A base i v + off)
      (Or.inr (by unfold rowCell scanAddress; omega))
    constructor
    · intro v hv i hi
      obtain ⟨d,rank⟩ := im.numbers v hv i hi
      exact ⟨by simpa only [Nat.add_zero] using (high i v 0).2.trans d, (high i v 2).1.trans rank⟩
    · intro i hi v hv
      obtain ⟨tag,data,p⟩ := im.parents i hi v hv
      refine ⟨by simpa only [Nat.add_zero] using (high i v 0).1.trans tag,(high i v 1).1.trans data,?_⟩
      intro u hu j
      change t.rm (rowCell A base i v + 4 + j.val) = _
      rw [Nat.add_assoc]
      exact ((high i v (4+j.val)).2).trans (by simpa only [Nat.add_assoc] using p u hu j)
  · intro j v hj
    have b : targetSlot k I.graph.n ≤ PrepareRAM.privateBase I ε := slot_before_call I ε _
    exact ((f _ (Or.inr (by omega))).1).trans (h.active j v hj)

theorem record_elsewhere {k : ℕ} {I : MultiInstance k} {ε : ℝ} {s t : Store} {v w : ℕ} (h : TargetRecord I ε w s) (hw : w ≠ v)
    (hn : ∀ x, x ≠ targetSlot k v → x ≠ targetSlot k v+1 → t.nm x = s.nm x)
    (hr : ∀ x, x ≠ targetSlot k v → t.rm x = s.rm x) : TargetRecord I ε w t := by
  have hn0 := hn (targetSlot k w) (by unfold targetSlot; omega) (by unfold targetSlot; omega)
  have hn1 := hn (targetSlot k w+1) (by unfold targetSlot; omega) (by unfold targetSlot; omega)
  have hr0 := hr (targetSlot k w) (by unfold targetSlot; omega)
  exact ⟨hn0.trans h.1,fun d hd => hr0.trans (h.2.1 d hd),fun r hp => hn1.trans (h.2.2 r hp)⟩

structure State {k : ℕ} (I : MultiInstance k) (ε : ℝ) (j : ℕ) (s : Store) : Prop where
  objects : Objects I ε s
  zero : s.nr 30 = 0
  one : s.nr 31 = 1
  count : s.nr 202 = (outerCalls I ε).length
  base : s.nr 200 = callBase I ε 0
  width : s.nr 207 = CallRAM.callWidth I ε
  cutoff : s.rr 89 = 3/4
  factor : s.rr 91 = 1+ε/4
  array : s.nr 34 = PrepareRAM.privateBase I ε + I.graph.n
  size : s.nr 35 = (incidentVertices I).length
  source : s.nr 209 = I.source
  index : s.nr 208 = j
  done : ∀ i < j, ∀ v, (incidentVertices I)[i]? = some v → TargetRecord I ε v s
  isolated : ∀ v < I.graph.n, v ∉ incidentVertices I → s.nm (targetSlot k v) = 0

theorem next_vertex {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε)
    (pos : hasPositiveBudget I = true) (j : ℕ) (hj : j < (incidentVertices I).length) (input : RAMInput) (s : Store)
    (h : State I ε j s) : ∃ t n, Run input (positiveVertex k (clockCoordinates I).length) s t n ∧ State I ε (j+1) t ∧
      n ≤ (clockCoordinates I).length + 13*(outerCalls I ε).length + 25 := by
  let v := (incidentVertices I)[j]
  have hget : (incidentVertices I)[j]? = some v := List.getElem?_eq_getElem hj
  have hv := List.mem_of_getElem? hget
  have inputs : Inputs I ε v s := ⟨h.zero,h.one,h.count,h.width,h.cutoff,h.factor,h.objects.calls,h.objects.tables⟩
  have read : s.nm (s.nr 34+s.nr 208) = v := by rw [h.array,h.index]; exact h.objects.active j v hget
  obtain ⟨t,n,hr,res,idx,nm,rm,hc⟩ := positive_vertex_run I hk ε hε pos v hv input s inputs read h.base h.source
  have nr (a : ℕ) (ha : FixedNat a) := hr.nat_frame a (vertex_registers _ _ a ha)
  have rr (a : ℕ) (ha : FixedReal a) := hr.real_frame a (vertex_reals _ _ a ha)
  refine ⟨t,n,hr,⟨h.objects.frame (target_frame I v (incident_valid I v hv) s t nm rm),
    (nr 30 (by unfold FixedNat; decide)).trans h.zero,(nr 31 (by unfold FixedNat; decide)).trans h.one,(nr 202 (by unfold FixedNat; decide)).trans h.count,
    (nr 200 (by unfold FixedNat; decide)).trans h.base,(nr 207 (by unfold FixedNat; decide)).trans h.width,(rr 89 (Or.inl rfl)).trans h.cutoff,
    (rr 91 (Or.inr rfl)).trans h.factor,(nr 34 (by unfold FixedNat; decide)).trans h.array,(nr 35 (by unfold FixedNat; decide)).trans h.size,
    (nr 209 (by unfold FixedNat; decide)).trans h.source,by rw [idx,h.index],?_,?_⟩,hc⟩
  · intro i hi w hw
    by_cases eq : w = v
    · exact eq ▸ res
    · have hij : i ≠ j := by intro hh; subst i; exact eq (Option.some.inj (hw.symm.trans hget))
      exact record_elsewhere (h.done i (by omega) w hw) eq nm rm
  · intro w hw hi
    have hh : w ≠ v := by intro e; exact hi (e ▸ hv)
    exact (nm _ (by unfold targetSlot; omega) (by unfold targetSlot; omega)).trans (h.isolated w hw hi)

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

def positiveLoop (k d : ℕ) := Cmd.loop (.nat .lt 208 35) (positiveVertex k d)

theorem targets_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (pos : hasPositiveBudget I = true)
    (remaining j : ℕ) (input : RAMInput) (s : Store) (hend : j+remaining = (incidentVertices I).length) (h : State I ε j s) :
    ∃ t n, Run input (positiveLoop k (clockCoordinates I).length) s t n ∧ State I ε (incidentVertices I).length t ∧
      n ≤ ((clockCoordinates I).length+13*(outerCalls I ε).length+27)*remaining+1 := by
  induction remaining generalizing j s with
  | zero =>
    rw [Nat.add_zero] at hend
    exact ⟨s,1,Run.loopFalse (by simp [Guard.eval,natTest,h.index,h.size,hend]),hend ▸ h,by simp⟩
  | succ m ih =>
    have lt : j < (incidentVertices I).length := by omega
    have g : (Guard.nat .lt 208 35).eval s = true := by simp [Guard.eval,natTest,h.index,h.size,lt]
    obtain ⟨p,c,hr,ph,hc⟩ := next_vertex I hk ε hε pos j lt input s h
    obtain ⟨t,b,he,th,hb⟩ := ih (j+1) p (by omega) ph
    refine ⟨t,_,Run.loopTrue g hr he,th,?_⟩
    rw [Nat.mul_succ]; omega

theorem inactive_branch {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (v : ℕ) (hv : v ∉ incidentVertices I)
    (pos : hasPositiveBudget I = true) : selectedBranch I ε v = .absent := by
  have hs : v ≠ I.source := fun h => hv (h ▸ incident_source_mem I)
  have no (r : ℕ) : acceptsIndex I ε v r = false := by
    cases ha : (outerCalls I ε)[r]? with
    | none => simp [acceptsIndex,ha]
    | some A =>
      have hI := (outerCalls_fields I ε hε A (List.mem_of_getElem? ha)).1
      cases acc : accepts A v with
      | false => simp [acceptsIndex,ha,acc]
      | true => exact False.elim (hv (hI ▸ accepts_incident A v acc))
  have empty : (List.range (outerCalls I ε).length).find? (acceptsIndex I ε v) = none :=
    List.find?_eq_none.mpr (fun r _ => by simp [no])
  simp only [selectedBranch,if_neg hs,pos,if_true]
  change (match (List.range (outerCalls I ε).length).find? (acceptsIndex I ε v) with
    | none => OutputBranch.absent | some r => .table r) = _
  rw [empty]

theorem encoding_of_records {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (s : Store) (h : Objects I ε s)
    (records : ∀ v < I.graph.n, TargetRecord I ε v s)
    (parents : hasPositiveBudget I = false → ∀ v ∈ incidentVertices I,
      s.nm (targetSlot k v + 2) = (((shortestTree I v).parent.map (· + 1)).getD 0)) :
    EncodesMultiOutput I ε (s.at 0) := by
  obtain ⟨⟨hq,hs,hn,hk,hρ,hγ⟩,hd,coords⟩ := h.header
  refine ⟨hq,hs,hn,hk,hd,h.calls.count,hρ,hγ,coords,records,parents,?_⟩
  intro r A ha
  obtain ⟨tag,thresh⟩ := h.calls.bounds r A ha
  have im := h.tables r (List.getElem?_eq_some_iff.mp ha).1 A ha
  obtain ⟨rfl,_,_⟩ := outerCalls_fields I ε hε A (List.mem_of_getElem? ha)
  refine ⟨thresh,tag,?_⟩
  intro v hv i hi
  obtain ⟨value,rank⟩ := im.numbers v hv i hi
  obtain ⟨pt,pd,pgt⟩ := im.parents i hi v hv
  exact ⟨value,pt,pd,rank,pgt⟩

theorem positive_encoding {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (pos : hasPositiveBudget I = true)
    (s : Store) (h : State I ε (incidentVertices I).length s) : EncodesMultiOutput I ε (s.at 0) := by
  apply encoding_of_records I ε hε s h.objects _ (by simp [pos])
  intro v hv
  by_cases hm : v ∈ incidentVertices I
  · exact h.done _ (List.idxOf_lt_length_of_mem hm) v (List.getElem?_idxOf hm)
  · have hb := inactive_branch I ε hε v hm pos
    exact ⟨by simpa [hb,outputTag] using h.isolated v hv hm,
      fun d hd => by simp [selectedDistance,hb] at hd,fun r hr => by simp [hb] at hr⟩

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM TableQuery

def saveActive : List Atom := [⟨.natCopy 34 142,trivial⟩,⟨.natCopy 35 143,trivial⟩]
def readyOps : List Atom :=
  [⟨.natCopy 200 49,trivial⟩,⟨.natCopy 207 58,trivial⟩,⟨.natConst 86 5,trivial⟩,⟨.loadNat 202 86,trivial⟩,
   ⟨.natConst 30 0,trivial⟩,⟨.natConst 31 1,trivial⟩,⟨.loadNat 209 31,trivial⟩,⟨.natConst 208 0,trivial⟩,
   ⟨.realConst 89 3,trivial⟩,⟨.realConst 92 4,trivial⟩,⟨.realOp .div 89 89 92,trivial⟩,
   ⟨.inputReal 91 30,trivial⟩,⟨.realOp .div 91 91 92,trivial⟩,⟨.realConst 93 1,trivial⟩,⟨.realOp .add 91 93 91,trivial⟩]
def positiveDim (k d : ℕ) := Cmd.seq (CallRAM.dimLayout k d) (.seq (.atoms readyOps) (positiveLoop k d))
def positive (k : ℕ) := Cmd.seq (.atoms saveActive) (.seq (.atoms dimensionOps) (selectDimension (positiveDim k) k))

theorem layout_safe (k d a : ℕ) (ha : a = 34 ∨ a = 35) : a ∉ (CallRAM.dimLayout k d).natWrites := by
  have pow (n : ℕ) : a ∉ (powers n).natWrites := by
    induction n with
    | zero => simp [powers,Cmd.natWrites]
    | succ n ih =>
      have h := stride_large n
      have hn : a ≠ strideReg n := by omega
      simp [powers,recordCmd,recordStride,productCmd,productInit,productLoop,productBody,productLast,Cmd.atoms,Cmd.natWrites,Atom.natWrites,hn,ih]
      omega
  have h1 := copies_preserve 58 60 (d+4) a (by omega)
  have h2 := copies_preserve 49 60 8 a (by omega)
  simp [CallRAM.dimLayout,SpaceRAM.shapeCmd,SpaceRAM.shapeOps,CallRAM.widthOps,Cmd.atoms,Cmd.natWrites,Atom.natWrites,pow,h1,h2]
  omega

theorem ready_state {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) (h : Objects I ε s)
    (blank : TargetArea I ε s) (array : s.nr 34 = PrepareRAM.privateBase I ε + I.graph.n)
    (size : s.nr 35 = (incidentVertices I).length) (base : s.nr 49 = callBase I ε 0) (width : s.nr 58 = CallRAM.callWidth I ε) :
    State I ε 0 (evalAtoms (multiInput I ε) readyOps s) := by
  let t := evalAtoms (multiInput I ε) readyOps s
  have count := h.calls.count
  have src : s.nm 1 = I.source := h.header.1.2.1
  have facts : t.nr 202 = (outerCalls I ε).length ∧ t.nr 200 = callBase I ε 0 ∧ t.nr 207 = CallRAM.callWidth I ε ∧
      t.rr 89 = 3/4 ∧ t.rr 91 = 1+ε/4 ∧ t.nr 209 = I.source := by
    simp [t,readyOps,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalReal,multiInput,count,src,base,width]
  refine ⟨h.frame (fun _ _ => ⟨rfl,rfl⟩),rfl,rfl,facts.1,facts.2.1,facts.2.2.1,facts.2.2.2.1,
    facts.2.2.2.2.1,array,size,facts.2.2.2.2.2,rfl,by intro i hi; omega,?_⟩
  intro v hv _
  exact (blank _ (by unfold targetSlot; omega) (by unfold callBase targetSlot; omega)).1

def positiveCost (k q d calls vertices : ℕ) := 4*k*q + 8*k + 60 + (d+13*calls+27)*vertices

theorem positive_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (pos : hasPositiveBudget I = true)
    (s : Store) (h : TableOutput I ε s) :
    ∃ t n, Run (multiInput I ε) (positive k) s t n ∧ EncodesMultiOutput I ε (t.at 0) ∧
      n ≤ positiveCost k (multiQ k ε) (clockCoordinates I).length (outerCalls I ε).length (incidentVertices I).length := by
  let input := multiInput I ε
  let d := (clockCoordinates I).length
  let p := evalAtoms input saveActive s
  let w := dimensioned p
  let v := marked w d
  have vd : w.nr 68 = d := h.hardware.header.2.1
  have hq : v.nm 0 = multiQ k ε := h.hardware.header.1.1
  have hn : v.nm 2 = I.graph.n := h.hardware.header.1.2.2.1
  obtain ⟨u,hu,base,width,_,nm,rm⟩ := CallRAM.dimension_layout_run k d input v
  have bu : u.nr 49 = callBase I ε 0 := by simpa only [callBase,Nat.zero_mul,Nat.add_zero,hn] using base
  have wu : u.nr 58 = CallRAM.callWidth I ε := by simpa only [d,CallRAM.callWidth,hn,hq] using width
  have obj : Objects I ε s := ⟨h.hardware.header,h.hardware.calls,h.tables,h.hardware.graph.vertices.value⟩
  have uobj : Objects I ε u := obj.frame (fun x _ => ⟨congrFun nm x,congrFun rm x⟩)
  have blank : TargetArea I ε u := fun x hl hh => ⟨(congrFun nm x).trans (h.targets x hl hh).1,(congrFun rm x).trans (h.targets x hl hh).2⟩
  have reg34 : v.nr 34 = s.nr 142 := rfl
  have reg35 : v.nr 35 = s.nr 143 := rfl
  have state := ready_state I ε u uobj blank ((hu.nat_frame 34 (layout_safe _ _ _ (Or.inl rfl))).trans (reg34.trans h.hardware.graph.vertices.array_reg))
    ((hu.nat_frame 35 (layout_safe _ _ _ (Or.inr rfl))).trans (reg35.trans h.hardware.graph.vertices.count_reg)) bu wu
  obtain ⟨t,c,ht,th,hc⟩ := targets_run I hk ε hε pos (incidentVertices I).length 0 input _ (by omega) state
  have hd : d ≤ k := clockCoordinates_length_le I
  have hx := Run.seq hu (Run.seq (run_atoms input readyOps u) ht)
  obtain ⟨b,hb,bc⟩ := select_dimension_run input (positiveDim k) k d hd w t _ vd hx
  refine ⟨t,2+(2+b),Run.seq (run_atoms input saveActive s) (Run.seq (dimension_run input p) hb),positive_encoding I ε hε pos t th,?_⟩
  change b ≤ d+21+d*(4*v.nm 0+5)+(15+c)+2*k+3 at bc
  rw [hq] at bc
  have le := Nat.mul_le_mul_right (multiQ k ε) hd
  change c ≤ (d+13*(outerCalls I ε).length+27)*(incidentVertices I).length+1 at hc
  unfold positiveCost
  change _ ≤ 4*k*multiQ k ε+8*k+60+(d+13*(outerCalls I ε).length+27)*(incidentVertices I).length
  nlinarith only [bc,hc,hd,le]

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace NearLinearRSP.TwoResources.Supplement.SelectionRAM
open Mission.Structured LayerRAM

noncomputable def coefficient (k : ℕ) : ℝ := SpaceRAM.reserveCoefficient k + 25 + 3*((k:ℝ)+27) +
  39*(12*(8192*(k:ℝ)+2)^(2*k))

theorem positive_bound {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (positiveCost k (multiQ k ε) (clockCoordinates I).length (outerCalls I ε).length (incidentVertices I).length : ℝ)
      ≤ coefficient k * multiScale I ε := by
  let M : ℝ := (max 1 I.graph.edges.length : ℕ)
  let V : ℝ := (incidentVertices I).length
  let C : ℝ := (outerCalls I ε).length
  let G : ℝ := (multiQ k ε + 1 : ℕ)
  let H := 1 + Real.log (max 2 I.graph.n : ℕ)
  let S := multiScale I ε
  have one : 1 ≤ S := SpaceRAM.scale_one I hk ε hε hε1
  have m : (I.graph.edges.length : ℝ) ≤ S := (PrepareRAM.graph_scales I ε hε hε1).1
  have maxLe : M ≤ S := by simpa [M,Nat.cast_max] using max_le one m
  have vertices : V ≤ 3*M := by
    have hi := incident_length_bound I
    dsimp only [V,M]; exact_mod_cast (show (incidentVertices I).length ≤ 3*max 1 I.graph.edges.length by omega)
  have vscale : V ≤ 3*S := vertices.trans (by linarith only [maxLe])
  have hlog : 1 ≤ H := by
    have hN : (1:ℝ) ≤ (max 2 I.graph.n : ℕ) := by exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
    dsimp [H]; linarith [Real.log_nonneg hN]
  have q : 1 ≤ G := by dsimp [G]; exact_mod_cast (show 1 ≤ multiQ k ε + 1 by omega)
  have m0 : 0 ≤ M := by dsimp [M]; positivity
  have c0 : 0 ≤ C := by dsimp [C]; positivity
  have cmp : M*C ≤ M*H*(C*G^(2*k)) := mul_le_mul
    (le_mul_of_one_le_right m0 hlog) (le_mul_of_one_le_right c0 (one_le_pow₀ q)) c0 (by positivity)
  have prod := cmp.trans (scaled_grid_work_bound I ε hε hε1)
  have vprod : V*C ≤ 3*(12*(8192*(k:ℝ)+2)^(2*k)*S) := by
    calc
      V*C ≤ 3*M*C := mul_le_mul_of_nonneg_right vertices c0
      _ = 3*(M*C) := by ring
      _ ≤ _ := by linarith only [prod]
  have front := SpaceRAM.reserve_bound I hk ε hε hε1 (4*k*multiQ k ε+8*k+35) (by omega)
  have hd : ((clockCoordinates I).length:ℝ) ≤ k := by exact_mod_cast clockCoordinates_length_le I
  have v0 : 0 ≤ V := by dsimp [V]; positivity
  have main := mul_le_mul (add_le_add_right hd 27) vscale v0 (show 0 ≤ 27+(k:ℝ) by positivity)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at front
  unfold positiveCost coefficient
  push_cast
  change 4*(k:ℝ)*(multiQ k ε:ℝ)+8*k+60+(((clockCoordinates I).length:ℝ)+13*C+27)*V ≤ _*S
  change _ ≤ SpaceRAM.reserveCoefficient k * S at front
  linarith only [front,one,main,vprod]

end NearLinearRSP.TwoResources.Supplement.SelectionRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured Mission.Preprocess
attribute [local instance] Classical.propDecidable

noncomputable def reduced {k : ℕ} (I : MultiInstance k) : Instance :=
  {lengthInstance I with cost := fun u v => if budgetAllow I u v then 0 else 1}

theorem reduced_allow {k : ℕ} (I : MultiInstance k) : (fun u v => decide ((reduced I).cost u v = 0)) = budgetAllow I := by
  funext u v
  cases h : budgetAllow I u v <;> simp [reduced,h]

theorem reduced_tree {k : ℕ} (I : MultiInstance k) : zeroBudgetTree (reduced I) = rankedShortest I := by
  exact congrArg (fun f => TwoResources.shortestTree (reduced I) f (fun u v => I.length u v)) (reduced_allow I)

theorem reduced_parents {k : ℕ} (I : MultiInstance k) (v : ℕ) :
    (zeroBudgetTree (reduced I) v).distance = (shortestTree I v).distance ∧
      (zeroBudgetTree (reduced I) v).parent = (shortestTree I v).parent := by
  rw [reduced_tree]; exact shortestTree_bridge I v

theorem inactive_distance {k : ℕ} (I : MultiInstance k) (v : ℕ) (hv : v ∉ incidentVertices I) :
    (shortestTree I v).distance = none := by
  cases e : (shortestTree I v).distance with
  | none => rfl
  | some d =>
    have hs : v ≠ I.source := fun h => hv (h ▸ incident_source_mem I)
    obtain ⟨u,a,_,_,_,edge,_,_⟩ := shortestTree_parent I v d hs e
    exact False.elim (hv (by
      change v ∈ activeVertices (lengthInstance I)
      exact activeVertices_edge_right (lengthInstance I) u v edge))

theorem no_calls {k : ℕ} (I : MultiInstance k) (ε : ℝ) : outerInputs (reduced I) ε = [] := by
  simp [outerInputs,reduced,lengthInstance]

theorem limit_le {k : ℕ} (hk : 0 < k) (ε : ℝ) : outerQ ε ≤ multiQ k ε := by
  apply Nat.ceil_mono
  change 512 / (ε / 4)^2 ≤ (512 * (k:ℝ)) / (ε / 4)^2
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  linarith

noncomputable def oldCost {k : ℕ} (I : MultiInstance k) (ε : ℝ) :=
  18*multiQ k ε + 14*(Nat.log 2 I.graph.n+1)^2 + 55*I.graph.edges.length + 3*LayerRAM.height I + 182 +
    (2*(15*LayerRAM.capacity I + (38*Nat.clog 2 (2*LayerRAM.capacity I)+58)*(incidentVertices I).length +
      (19*Nat.clog 2 (2*LayerRAM.capacity I)+46)*I.graph.edges.length+7)+6)

def treeCommand := Cmd.seq setupCmd zeroTreesCmd

structure Labels {k : ℕ} (I : MultiInstance k) (s : Store) : Prop where
  labels : ∀ v ∈ incidentVertices I, Mission.TargetRecords.LabelRep (shortestTree I v).distance (s.rr 281) (s.rm (targetAddress v+3))
  parents : ∀ v ∈ incidentVertices I, s.nm (targetAddress v+3) = ((shortestTree I v).parent.map (·+1)).getD 0

theorem tree_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s n, Run (encodeInput (reduced I) ε) treeCommand initialStore s n ∧ Labels I s ∧ n ≤ oldCost I ε := by
  let J := reduced I
  obtain ⟨p,a,hp,setup,ha⟩ := setupCmd_run J ε hε hε1
  obtain ⟨s,b,hb,_,pars,labels,_,_,_,bc⟩ := zeroTrees_ready J ε p setup
  refine ⟨s,a+b,Run.seq hp hb,⟨?_,?_⟩,?_⟩
  · intro v hv
    rw [← (reduced_parents I v).1]
    exact (labels.labels v hv).2
  · intro v hv
    rw [← (reduced_parents I v).2]
    exact (pars v hv).2
  · change a ≤ 18*outerQ ε+14*(Nat.log 2 I.graph.n+1)^2+55*I.graph.edges.length+
      8*(outerInputs J ε).length+3*LayerRAM.height I+182 at ha
    change b ≤ 2*(15*LayerRAM.capacity I + (38*Nat.clog 2 (2*LayerRAM.capacity I)+58)*(incidentVertices I).length +
      (19*Nat.clog 2 (2*LayerRAM.capacity I)+46)*I.graph.edges.length+7)+6 at bc
    have eq : outerInputs J ε = [] := no_calls I ε
    rw [eq] at ha
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at ha
    have hq := limit_le hk ε
    unfold oldCost; omega

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.SeparatedRAM
open Mission.Structured

def memAddr (base a : ℕ) := base+2*a
def inputAddr (base a : ℕ) := base+2*a+1
def view (b base : ℕ) (s : Store) : Store :=
  ⟨fun a => s.nr (b+a),fun a => s.rr (b+a),fun a => s.nm (memAddr base a),fun a => s.rm (memAddr base a)⟩

structure Region (base : ℕ) (input : RAMInput) (s : Store) : Prop where
  work : s.nr 189 = base
  source : s.nr 220 = base+1
  nats : ∀ a, s.nm (inputAddr base a) = input.naturals a
  reals : ∀ a, s.rm (inputAddr base a) = input.reals a

structure Frame (b base : ℕ) (s t : Store) : Prop where
  nr : ∀ a < b, a ≠ 224 → t.nr a = s.nr a
  rr : ∀ a < b, t.rr a = s.rr a
  memory : ∀ x, (∀ j, x ≠ memAddr base j) → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem Frame.refl (b base : ℕ) (s : Store) : Frame b base s s := ⟨fun _ _ _ => rfl,fun _ _ => rfl,fun _ _ => ⟨rfl,rfl⟩⟩
theorem Frame.trans {b base : ℕ} {s t u : Store} (f : Frame b base s t) (g : Frame b base t u) : Frame b base s u := by
  refine ⟨fun a ha h => (g.nr a ha h).trans (f.nr a ha h),fun a ha => (g.rr a ha).trans (f.rr a ha),?_⟩
  intro x hx; exact ⟨(g.memory x hx).1.trans (f.memory x hx).1,(g.memory x hx).2.trans (f.memory x hx).2⟩

theorem Region.frame {b base : ℕ} {s t : Store} {input : RAMInput} (h : Region base input s) (f : Frame b base s t)
    (hb : 224 < b) : Region base input t := by
  have safe (a j : ℕ) : inputAddr base a ≠ memAddr base j := by unfold inputAddr memAddr; omega
  exact ⟨(f.nr 189 (by omega) (by decide)).trans h.work,(f.nr 220 (by omega) (by decide)).trans h.source,
    fun a => (f.memory _ (safe a)).1.trans (h.nats a),fun a => (f.memory _ (safe a)).2.trans (h.reals a)⟩

def address (b baseReg a : ℕ) : List Atom :=
  [⟨.natOp .add 224 (b+a) (b+a),trivial⟩,⟨.natOp .add 224 baseReg 224,trivial⟩]

def ops (b : ℕ) (a : Atom) : List Atom :=
  match a.val with
  | .loadNat d j => address b 189 j ++ [⟨.loadNat (b+d) 224,trivial⟩]
  | .loadReal d j => address b 189 j ++ [⟨.loadReal (b+d) 224,trivial⟩]
  | .storeNat j r => address b 189 j ++ [⟨.storeNat 224 (b+r),trivial⟩]
  | .storeReal j r => address b 189 j ++ [⟨.storeReal 224 (b+r),trivial⟩]
  | .inputNat d j => address b 220 j ++ [⟨.loadNat (b+d) 224,trivial⟩]
  | .inputReal d j => address b 220 j ++ [⟨.loadReal (b+d) 224,trivial⟩]
  | _ => [RegisterShift.atom b a]

theorem ops_length (b : ℕ) (a : Atom) : (ops b a).length ≤ 3 := by rcases a with ⟨i,hi⟩; cases i <;> first | exact le_rfl | exact (by decide : 1 ≤ 3)

theorem view_mem_update {α : Type} (f : ℕ → α) (base x : ℕ) (v : α) :
    (fun j => Function.update f (memAddr base x) v (memAddr base j)) = Function.update (fun j => f (memAddr base j)) x v := by
  funext j
  by_cases h : j = x
  · subst j; simp
  · have hn : memAddr base j ≠ memAddr base x := by unfold memAddr; omega
    simp [Function.update_of_ne h,Function.update_of_ne hn]

theorem atom_view (b base : ℕ) (hb : 224 < b) (a : Atom) (orig input : RAMInput) (s : Store) (h : Region base orig s) :
    view b base (evalAtoms input (ops b a) s) = a.eval orig (view b base s) := by
  have high (j : ℕ) : b+j ≠ 224 := by omega
  have e (j : ℕ) : base + (j+j) = memAddr base j := by unfold memAddr; omega
  have o (j : ℕ) : base+1+(j+j) = inputAddr base j := by unfold inputAddr; omega
  rcases a with ⟨i,hi⟩
  cases i <;> try contradiction
  all_goals simp [view,ops,address,RegisterShift.atom,RegisterShift.instr,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,
    evalNat,RegisterShift.view_update,Function.update_of_ne (high _),h.work,h.source,e,o,h.nats,h.reals,view_mem_update]

theorem atom_frame (b base : ℕ) (hb : 224 < b) (a : Atom) (orig input : RAMInput) (s : Store) (h : Region base orig s) :
    Frame b base s (evalAtoms input (ops b a) s) := by
  have high (j : ℕ) : b+j ≠ 224 := by omega
  have e (j : ℕ) : base + (j+j) = memAddr base j := by unfold memAddr; omega
  rcases a with ⟨i,hi⟩
  cases i <;> try contradiction
  all_goals constructor
  all_goals first
    | intro j hj htmp
      have ne (r : ℕ) : j ≠ b+r := by omega
      simp [ops,address,RegisterShift.atom,RegisterShift.instr,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,Function.update_of_ne (ne _),Function.update_of_ne htmp]
    | intro j hj
      first
      | have ne (r : ℕ) : j ≠ b+r := by omega
        simp [ops,address,RegisterShift.atom,RegisterShift.instr,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,Function.update_of_ne (ne _)]
      | simp [ops,address,RegisterShift.atom,RegisterShift.instr,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,evalNat,h.work,e,Function.update_of_ne (hj _),Function.update_of_ne (high _)]

end NearLinearRSP.TwoResources.Supplement.SeparatedRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.SeparatedRAM
open Mission.Structured

def program (b : ℕ) : Cmd → Cmd
  | .skip => .skip
  | .atom a => .atoms (ops b a)
  | .seq c d => .seq (program b c) (program b d)
  | .branch g c d => .branch (RegisterShift.guardAt b g) (program b c) (program b d)
  | .loop g c => .loop (RegisterShift.guardAt b g) (program b c)

theorem guard_view (b base : ℕ) (g : Guard) (s : Store) : (RegisterShift.guardAt b g).eval s = g.eval (view b base s) := by
  cases g <;> rfl

theorem program_run {orig : RAMInput} {c : Cmd} {s t : Store} {n : ℕ} (run : Run orig c s t n)
    (b base : ℕ) (hb : 224 < b) (input : RAMInput) (x : Store) (hx : view b base x = s) (h : Region base orig x) :
    ∃ y steps, Run input (program b c) x y steps ∧ view b base y = t ∧ Frame b base x y ∧ steps ≤ 3*n := by
  induction run generalizing x with
  | skip s => exact ⟨x,0,Run.skip x,hx,Frame.refl _ _ _,by decide⟩
  | atom a s => exact ⟨_,_,run_atoms input (ops b a) x,by rw [atom_view b base hb a orig input x h,hx],
      atom_frame b base hb a orig input x h,ops_length b a⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    obtain ⟨u,a,hu,hv,hf,ha⟩ := ih₁ x hx h
    obtain ⟨y,m,hy,hw,hg,hm⟩ := ih₂ u hv (h.frame hf hb)
    exact ⟨y,_,Run.seq hu hy,hw,hf.trans hg,by omega⟩
  | branchTrue g he ih =>
    obtain ⟨y,m,hy,hv,hf,hm⟩ := ih x hx h
    exact ⟨y,_,Run.branchTrue (by rw [guard_view b base,hx]; exact g) hy,hv,hf,by omega⟩
  | branchFalse g he ih =>
    obtain ⟨y,m,hy,hv,hf,hm⟩ := ih x hx h
    exact ⟨y,_,Run.branchFalse (by rw [guard_view b base,hx]; exact g) hy,hv,hf,by omega⟩
  | loopFalse g => exact ⟨x,1,Run.loopFalse (by rw [guard_view b base,hx]; exact g),hx,Frame.refl _ _ _,by decide⟩
  | loopTrue g h₁ h₂ ih₁ ih₂ =>
    obtain ⟨u,a,hu,hv,hf,ha⟩ := ih₁ x hx h
    obtain ⟨y,m,hy,hw,hg,hm⟩ := ih₂ u hv (h.frame hf hb)
    exact ⟨y,_,Run.loopTrue (by rw [guard_view b base,hx]; exact g) hu hy,hw,hf.trans hg,by omega⟩

end NearLinearRSP.TwoResources.Supplement.SeparatedRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured SeparatedRAM

def initialWords {α : Type} [Zero α] (f : ℕ → α) (n a : ℕ) : α := if a < n then f a else 0
def pair {α : Type} (f : ℕ → α) (a : ℕ) (x y : α) := Function.update (Function.update f a x) (a+2) y

theorem next_addr (b a : ℕ) : inputAddr b (a+1) = inputAddr b a + 2 := by unfold inputAddr; omega

theorem read_pair {α : Type} [Zero α] (f g : ℕ → α) (b p : ℕ) (h : ∀ a, g (inputAddr b a) = initialWords f p a) (a : ℕ) :
    pair g (inputAddr b p) (f p) (f (p+1)) (inputAddr b a) = initialWords f (p+2) a := by
  by_cases h0 : a = p
  · subst a
    simp [pair,initialWords,Function.update_of_ne (show inputAddr b p ≠ inputAddr b p+2 by omega)]
  · by_cases h1 : a = p+1
    · subst a; simp [pair,initialWords,next_addr]
    · have ne0 : inputAddr b a ≠ inputAddr b p := by unfold inputAddr; omega
      have ne1 : inputAddr b a ≠ inputAddr b p+2 := by unfold inputAddr; omega
      have same : a < p+2 ↔ a < p := by omega
      simp [pair,Function.update_of_ne ne0,Function.update_of_ne ne1,h,initialWords,same]

def OffInput (b : ℕ) (s t : Store) : Prop := ∀ x, (∀ a, x ≠ inputAddr b a) → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem OffInput.trans {b : ℕ} {s t u : Store} (h : OffInput b s t) (g : OffInput b t u) : OffInput b s u :=
  fun x hx => ⟨(g x hx).1.trans (h x hx).1,(g x hx).2.trans (h x hx).2⟩

theorem pair_off {α : Type} (f : ℕ → α) (b p x : ℕ) (v w : α) (hx : ∀ a, x ≠ inputAddr b a) :
    pair f (inputAddr b p) v w x = f x := by
  have h1 : x ≠ inputAddr b p+2 := by rw [← next_addr]; exact hx _
  simp [pair,Function.update_of_ne h1,Function.update_of_ne (hx _)]

structure PackState {k : ℕ} (I : MultiInstance k) (ε : ℝ) (base j : ℕ) (s : Store) : Prop where
  baseReg : s.nr 189 = base
  inputReg : s.nr 220 = base+1
  one : s.nr 31 = 1
  two : s.nr 236 = 2
  dim : s.nr 234 = k
  cursor : s.nr 230 = j
  total : s.nr 231 = I.graph.edges.length
  endpoints : s.nr 232 = 4+2*j
  weight : s.nr 70 = InputValues.row k j
  place : s.nr 233 = inputAddr base (2+2*j)
  nats : ∀ a, s.nm (inputAddr base a) = initialWords (encodeInput (reduced I) ε).naturals (3+2*j) a
  reals : ∀ a, s.rm (inputAddr base a) = initialWords (encodeInput (reduced I) ε).reals (2+2*j) a

theorem PackState.copy {k : ℕ} {I : MultiInstance k} {ε : ℝ} {b j : ℕ} {s t : Store} (h : PackState I ε b j s)
    (nr : ∀ a, a ∈ [189,220,31,236,234,230,231,232,70,233] → t.nr a = s.nr a)
    (nm : t.nm = s.nm) (rm : t.rm = s.rm) : PackState I ε b j t :=
  ⟨(nr _ (by decide)).trans h.baseReg,(nr _ (by decide)).trans h.inputReg,(nr _ (by decide)).trans h.one,
   (nr _ (by decide)).trans h.two,(nr _ (by decide)).trans h.dim,(nr _ (by decide)).trans h.cursor,
   (nr _ (by decide)).trans h.total,(nr _ (by decide)).trans h.endpoints,(nr _ (by decide)).trans h.weight,
   (nr _ (by decide)).trans h.place,fun a => (congrFun nm _).trans (h.nats a),fun a => (congrFun rm _).trans (h.reals a)⟩

theorem packed_region {k : ℕ} (I : MultiInstance k) (ε : ℝ) (base : ℕ) (s : Store)
    (h : PackState I ε base I.graph.edges.length s) : Region base (encodeInput (reduced I) ε) s := by
  refine ⟨h.baseReg,h.inputReg,?_,?_⟩
  · intro a
    rw [h.nats,initialWords]
    split <;> rename_i hh
    · rfl
    · have hn : (reduced I).graph.edges[(a-3)/2]? = none := List.getElem?_eq_none (by change I.graph.edges.length ≤ (a-3)/2; omega)
      simp [encodeInput,show a ≠ 0 by omega,show a ≠ 1 by omega,show a ≠ 2 by omega,hn]
  · intro a
    rw [h.reals,initialWords]
    split <;> rename_i hh
    · rfl
    · have hn : (reduced I).graph.edges[(a-2)/2]? = none := List.getElem?_eq_none (by change I.graph.edges.length ≤ (a-2)/2; omega)
      simp [encodeInput,show a ≠ 0 by omega,show a ≠ 1 by omega,hn]

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured SeparatedRAM

def packHeader (k : ℕ) : List Atom :=
  [⟨.natConst 30 0,trivial⟩,⟨.natConst 31 1,trivial⟩,⟨.natConst 236 2,trivial⟩,⟨.natConst 234 k,trivial⟩,
   ⟨.natConst 70 k,trivial⟩,⟨.natConst 230 0,trivial⟩,⟨.natConst 232 4,trivial⟩,⟨.natOp .add 220 189 31,trivial⟩,
   ⟨.inputNat 87 30,trivial⟩,⟨.storeNat 220 87,trivial⟩,⟨.inputReal 76 30,trivial⟩,⟨.storeReal 220 76,trivial⟩,
   ⟨.inputNat 231 31,trivial⟩,⟨.natOp .add 86 220 236,trivial⟩,⟨.storeNat 86 231,trivial⟩,
   ⟨.inputNat 87 236,trivial⟩,⟨.natOp .add 233 86 236,trivial⟩,⟨.storeNat 233 87,trivial⟩]

theorem pack_header_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (base : ℕ) (s : Store) (hb : s.nr 189 = base)
    (blank : ∀ x, base ≤ x → s.nm x = 0 ∧ s.rm x = 0) :
    let t := evalAtoms (multiInput I ε) (packHeader k) s
    PackState I ε base 0 t ∧ OffInput base s t := by
  let t := evalAtoms (multiInput I ε) (packHeader k) s
  have nr : t.nm = Function.update (Function.update (Function.update s.nm (inputAddr base 0) I.graph.n)
      (inputAddr base 1) I.graph.edges.length) (inputAddr base 2) I.source := by
    simp [t,packHeader,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hb,multiInput,inputAddr,Nat.add_assoc]
  have rr : t.rm = Function.update s.rm (inputAddr base 0) ε := by
    simp [t,packHeader,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hb,multiInput,inputAddr]
  have regs : t.nr 189 = base ∧ t.nr 220 = base+1 ∧ t.nr 231 = I.graph.edges.length ∧ t.nr 233 = inputAddr base 2 := by
    simp [t,packHeader,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,hb,multiInput,inputAddr,Nat.add_assoc]
  refine ⟨⟨regs.1,regs.2.1,rfl,rfl,rfl,rfl,regs.2.2.1,rfl,by simp [t,packHeader,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,InputValues.row],regs.2.2.2,?_,?_⟩,?_⟩
  · intro a; change t.nm _ = _
    rw [nr]
    have ne (i : ℕ) (h : a ≠ i) : inputAddr base a ≠ inputAddr base i := by unfold inputAddr; omega
    have ni (i j : ℕ) (h : i ≠ j) : inputAddr base i ≠ inputAddr base j := by unfold inputAddr; omega
    by_cases h0 : a = 0
    · subst a; simp [initialWords,encodeInput,reduced,lengthInstance,Function.update_of_ne (ni 0 1 (by decide)),Function.update_of_ne (ni 0 2 (by decide))]
    by_cases h1 : a = 1
    · subst a; simp [initialWords,encodeInput,reduced,lengthInstance,Function.update_of_ne (ni 1 2 (by decide))]
    by_cases h2 : a = 2
    · subst a; simp [initialWords,encodeInput,reduced,lengthInstance]
    have ht : ¬ a < 3 := by omega
    simp [initialWords,Function.update_of_ne (ne 0 h0),Function.update_of_ne (ne 1 h1),Function.update_of_ne (ne 2 h2),ht,
      (blank _ (show base ≤ inputAddr base a by unfold inputAddr; omega)).1]
  · intro a; change t.rm _ = _
    rw [rr]
    by_cases h0 : a = 0
    · subst a; simp [initialWords,encodeInput]
    have ne : inputAddr base a ≠ inputAddr base 0 := by unfold inputAddr; omega
    rw [Function.update_of_ne ne,(blank _ (show base ≤ inputAddr base a by unfold inputAddr; omega)).2]
    by_cases h1 : a = 1
    · subst a; simp [initialWords,encodeInput,reduced,lengthInstance]
    · simp [initialWords,show ¬ a < 2 by omega]
  · intro x hx
    change t.nm x = _ ∧ t.rm x = _
    simp [nr,rr,Function.update_of_ne (hx _)]

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2100000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured SeparatedRAM

def flagStart : List Atom := [⟨.natConst 71 1,trivial⟩,⟨.realConst 74 0,trivial⟩,⟨.natConst 30 0,trivial⟩]
def flagReal := Cmd.branch (.nat .eq 71 30) (.atom ⟨.realConst 75 1,trivial⟩) (.atom ⟨.realConst 75 0,trivial⟩)
def edgeFlag (k : ℕ) := Cmd.seq (.atoms flagStart) (.seq (EdgeRAM.tests (List.range (k-1))) flagReal)

theorem edge_flag_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (base j : ℕ) (e : ℕ × ℕ) (he : I.graph.edges[j]? = some e)
    (s : Store) (h : PackState I ε base j s) :
    ∃ t n, Run (multiInput I ε) (edgeFlag k) s t n ∧ PackState I ε base j t ∧
      t.rr 75 = (reduced I).cost e.1 e.2 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧ n ≤ 8*k+6 := by
  classical
  let input := multiInput I ε
  let p := evalAtoms input flagStart s
  let rs := List.range (k-1)
  obtain ⟨u,n,hu,flag,hc⟩ := EdgeRAM.tests_run input rs p rfl
  have cn := EdgeRAM.tests_readonly rs
  have nm : u.nm = s.nm := hu.natMemory_frame cn.1
  have rm : u.rm = s.rm := hu.realMemory_frame cn.2
  have pass : (∀ r ∈ rs, EdgeRAM.Pass input (p.nr 70) r) ↔ ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0 := by
    have row : p.nr 70 = InputValues.row k j := h.weight
    rw [row]; exact EdgeRAM.input_passes I ε j e he
  have ph : PackState I ε base j u := h.copy (fun a ha =>
    (hu.nat_frame a (EdgeRAM.tests_registers rs a (by simp at ha; omega) (by simp at ha; omega))).trans
      (by simp [p,flagStart,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,Function.update_of_ne (show a ≠ 71 by simp at ha; omega),
        Function.update_of_ne (show a ≠ 30 by simp at ha; omega)])) nm rm
  have z : u.nr 30 = 0 := hu.nat_frame 30 (EdgeRAM.tests_registers _ _ (by decide) (by decide))
  have one : p.nr 71 = 1 := rfl
  have ic : rs.length = k-1 := List.length_range
  rw [ic] at hc
  by_cases allow : ∀ r, I.budget r = 0 → I.cost r e.1 e.2 = 0
  · have f : u.nr 71 = 1 := by rw [flag,if_pos (pass.mpr allow),one]
    have g : (Guard.nat .eq 71 30).eval u = false := by simp [Guard.eval,natTest,f,z]
    have bv : budgetAllow I e.1 e.2 = true := decide_eq_true allow
    let a : Atom := ⟨.realConst 75 0,trivial⟩
    exact ⟨_,_,Run.seq (run_atoms input flagStart s) (Run.seq hu (Run.branchFalse g (Run.atom a u))),ph.copy (fun _ _ => rfl) rfl rfl,
      by simp [a,Atom.eval,Store.ofRAM,Store.at,ramStep,reduced,bv],nm,rm,
      by change 3+(n+(1+1)) ≤ 8*k+6; omega⟩
  · have f : u.nr 71 = 0 := by rw [flag,if_neg (fun h => allow (pass.mp h))]
    have g : (Guard.nat .eq 71 30).eval u = true := by simp [Guard.eval,natTest,f,z]
    have bv : budgetAllow I e.1 e.2 = false := decide_eq_false allow
    let a : Atom := ⟨.realConst 75 1,trivial⟩
    exact ⟨_,_,Run.seq (run_atoms input flagStart s) (Run.seq hu (Run.branchTrue g (Run.atom a u))),ph.copy (fun _ _ => rfl) rfl rfl,
      by simp [a,Atom.eval,Store.ofRAM,Store.at,ramStep,reduced,bv],nm,rm,
      by change 3+(n+(1+1+1)) ≤ 8*k+6; omega⟩

def writeEdge : List Atom :=
  [⟨.inputReal 76 70,trivial⟩,⟨.storeReal 233 76,trivial⟩,⟨.natOp .add 86 233 236,trivial⟩,
   ⟨.storeReal 86 75,trivial⟩,⟨.inputNat 87 232,trivial⟩,⟨.storeNat 86 87,trivial⟩,
   ⟨.natOp .add 86 86 236,trivial⟩,⟨.natOp .add 88 232 31,trivial⟩,⟨.inputNat 87 88,trivial⟩,⟨.storeNat 86 87,trivial⟩,
   ⟨.natCopy 233 86,trivial⟩,⟨.natOp .add 232 232 236,trivial⟩,⟨.natOp .add 70 70 234,trivial⟩,⟨.natOp .add 230 230 31,trivial⟩]
def packEdge (k : ℕ) := Cmd.seq (edgeFlag k) (.atoms writeEdge)

theorem write_edge_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (base j : ℕ) (e : ℕ × ℕ)
    (he : I.graph.edges[j]? = some e) (s : Store) (h : PackState I ε base j s) (flag : s.rr 75 = (reduced I).cost e.1 e.2) :
    let t := evalAtoms (multiInput I ε) writeEdge s
    PackState I ε base (j+1) t ∧ OffInput base s t := by
  let input := multiInput I ε
  let t := evalAtoms input writeEdge s
  let old := encodeInput (reduced I) ε
  let n := 3+2*j
  let r := 2+2*j
  have ends := InputValues.edge_endpoints I ε j e he
  have len := InputValues.row_length I hk ε j e he
  have oldn : old.naturals n = e.1 := encodeInput_edge_left (reduced I) ε j e he
  have oldn' : old.naturals (n+1) = e.2 := encodeInput_edge_right (reduced I) ε j e he
  have oldr : old.reals r = I.length e.1 e.2 := encodeInput_length (reduced I) ε j e he
  have oldr' : old.reals (r+1) = (reduced I).cost e.1 e.2 := encodeInput_cost (reduced I) ε j e he
  have places : inputAddr base (2+2*j)+2 = inputAddr base n := by unfold inputAddr n; omega
  have nm : t.nm = pair s.nm (inputAddr base n) (old.naturals n) (old.naturals (n+1)) := by
    simp [t,input,writeEdge,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,h.two,h.one,h.place,h.endpoints,
      oldn,oldn',ends.1,ends.2,pair,places]
  have rm : t.rm = pair s.rm (inputAddr base r) (old.reals r) (old.reals (r+1)) := by
    simp [t,input,writeEdge,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,h.two,h.place,h.weight,oldr,oldr',flag,len,pair,r]
  have regs : t.nr 230 = j+1 ∧ t.nr 232 = 4+2*(j+1) ∧ t.nr 70 = InputValues.row k (j+1) ∧ t.nr 233 = inputAddr base (2+2*(j+1)) := by
    simp [t,writeEdge,evalAtoms,Atom.eval,Store.ofRAM,Store.at,ramStep,evalNat,h.cursor,h.endpoints,h.weight,h.place,h.one,h.two,h.dim,InputValues.row,inputAddr,Nat.mul_succ]
    omega
  refine ⟨⟨h.baseReg,h.inputReg,h.one,h.two,h.dim,regs.1,h.total,regs.2.1,regs.2.2.1,regs.2.2.2,?_,?_⟩,?_⟩
  · intro a; change t.nm _ = _
    rw [nm]; simpa only [show 3+2*(j+1) = n+2 by unfold n; omega] using read_pair old.naturals s.nm base n h.nats a
  · intro a; change t.rm _ = _
    rw [rm]; simpa only [show 2+2*(j+1) = r+2 by unfold r; omega] using read_pair old.reals s.rm base r h.reals a
  · intro x hx; change t.nm x = _ ∧ t.rm x = _
    rw [nm,rm]; exact ⟨pair_off _ _ _ _ _ _ hx,pair_off _ _ _ _ _ _ hx⟩

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured SeparatedRAM LayerRAM

def packLoop (k : ℕ) := Cmd.loop (.nat .lt 230 231) (packEdge k)
def pack (k : ℕ) := Cmd.seq (.atoms (packHeader k)) (packLoop k)
def modeOps : List Atom := [⟨.natConst 86 5,trivial⟩,⟨.loadNat 86 86,trivial⟩,⟨.natConst 30 0,trivial⟩]
def preludeCmd (k : ℕ) := Cmd.seq (constructAll k) (.seq (.atoms modeOps) (pack k))
def bank (k : ℕ) := 225 + (preludeCmd k).natWrites.sup id + (preludeCmd k).realWrites.sup id

theorem pack_loop_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (base remaining j : ℕ) (s : Store)
    (endIndex : j+remaining = I.graph.edges.length) (h : PackState I ε base j s) :
    ∃ t n, Run (multiInput I ε) (packLoop k) s t n ∧ PackState I ε base I.graph.edges.length t ∧ OffInput base s t ∧
      n ≤ (8*k+22)*remaining+1 := by
  induction remaining generalizing s j with
  | zero =>
    rw [Nat.add_zero] at endIndex
    exact ⟨s,1,Run.loopFalse (by simp [Guard.eval,natTest,h.cursor,h.total,endIndex]),endIndex ▸ h,fun _ _ => ⟨rfl,rfl⟩,by simp⟩
  | succ l ih =>
    have lt : j < I.graph.edges.length := by omega
    let e := I.graph.edges[j]
    have he : I.graph.edges[j]? = some e := List.getElem?_eq_getElem lt
    obtain ⟨p,a,hp,ph,flag,nm,rm,hc⟩ := edge_flag_run I ε base j e he s h
    obtain ⟨next,off⟩ := write_edge_run I hk ε base j e he p ph flag
    obtain ⟨t,c,ht,th,tf,tc⟩ := ih (j+1) _ (by omega) next
    have g : (Guard.nat .lt 230 231).eval s = true := by simp [Guard.eval,natTest,h.cursor,h.total,lt]
    have pf : OffInput base s p := fun x _ => ⟨congrFun nm x,congrFun rm x⟩
    refine ⟨t,_,Run.loopTrue g (Run.seq hp (run_atoms _ writeEdge p)) ht,th,pf.trans (off.trans tf),?_⟩
    change 1+(a+14)+1+c ≤ _; rw [Nat.mul_succ]; omega

theorem pack_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (base : ℕ) (s : Store)
    (reg : s.nr 189 = base) (blank : ∀ x, base ≤ x → s.nm x = 0 ∧ s.rm x = 0) :
    ∃ t n, Run (multiInput I ε) (pack k) s t n ∧ Region base (encodeInput (reduced I) ε) t ∧ OffInput base s t ∧
      n ≤ (8*k+22)*I.graph.edges.length+19 := by
  obtain ⟨p,f⟩ := pack_header_run I ε base s reg blank
  obtain ⟨t,n,hr,h,frame,cost⟩ := pack_loop_run I hk ε base I.graph.edges.length 0 _ (by omega) p
  exact ⟨t,18+n,Run.seq (run_atoms _ _ _) hr,packed_region I ε base t h,f.trans frame,by omega⟩

theorem bank_high (k : ℕ) : 224 < bank k := by unfold bank; omega

theorem empty_registers {k n : ℕ} {I : MultiInstance k} {ε : ℝ} {s : Store}
    (h : Run (multiInput I ε) (preludeCmd k) initialStore s n) (r : ℕ) : s.nr (bank k+r) = 0 ∧ s.rr (bank k+r) = 0 := by
  have nn : bank k+r ∉ (preludeCmd k).natWrites := by
    intro hm
    have hh : bank k+r ≤ (preludeCmd k).natWrites.sup id := Finset.le_sup (f:=id) hm
    unfold bank at hh; omega
  have rr : bank k+r ∉ (preludeCmd k).realWrites := by
    intro hm
    have hh : bank k+r ≤ (preludeCmd k).realWrites.sup id := Finset.le_sup (f:=id) hm
    unfold bank at hh; omega
  exact ⟨h.nat_frame _ nn,h.real_frame _ rr⟩

theorem pack_active_registers (k a : ℕ) (ha : a = 142 ∨ a = 143) : a ∉ (pack k).natWrites := by
  have fh := EdgeRAM.tests_registers (List.range (k-1)) a (by omega) (by omega)
  simp [pack,packHeader,packLoop,packEdge,edgeFlag,flagStart,flagReal,writeEdge,Cmd.atoms,Cmd.natWrites,Atom.natWrites,fh]
  omega

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured Mission.TargetRecords SeparatedRAM LayerRAM SelectionRAM

structure TreeView {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  labels : ∀ v ∈ incidentVertices I, LabelRep (shortestTree I v).distance (s.rr (bank k+281)) (s.rm (memAddr (keyBase I ε) (targetAddress v + 3)))
  parents : ∀ v ∈ incidentVertices I, s.nm (memAddr (keyBase I ε) (targetAddress v + 3)) = ((shortestTree I v).parent.map (·+1)).getD 0

structure TreeOutput {k : ℕ} (I : MultiInstance k) (ε : ℝ) (s : Store) : Prop where
  objects : Objects I ε s
  tree : TreeView I ε s
  keys : s.nr 189 = keyBase I ε
  array : s.nr 142 = PrepareRAM.privateBase I ε + I.graph.n
  size : s.nr 143 = (incidentVertices I).length
  isolated : ∀ v < I.graph.n, v ∉ incidentVertices I → s.nm (targetSlot k v) = 0

def ordinaryTree (k : ℕ) := Cmd.seq (pack k) (program (bank k) treeCommand)

theorem tree_image_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hz : hasPositiveBudget I = false)
    (s : Store) (h : TableOutput I ε s) (a : ℕ) (prefixRun : Run (multiInput I ε) (constructAll k) initialStore s a) :
    let x := evalAtoms (multiInput I ε) modeOps s
    ∃ t n, Run (multiInput I ε) (ordinaryTree k) x t n ∧ TreeOutput I ε t ∧ n ≤ (8*k+22)*I.graph.edges.length+19+3*oldCost I ε := by
  let input := multiInput I ε
  let x := evalAtoms input modeOps s
  let base := keyBase I ε
  let B := bank k
  have calls : outerCalls I ε = [] := by simp [outerCalls,hz]
  have zero : (outerCalls I ε).length = 0 := by rw [calls]; rfl
  obtain ⟨p,m,hp,region,off,mc⟩ := pack_run I hk ε base x h.hardware.keys (h.emptySpace zero)
  have pre : Run input (preludeCmd k) initialStore p (a+(3+m)) := Run.seq prefixRun (Run.seq (run_atoms _ _ _) hp)
  have even (j a : ℕ) : memAddr base j ≠ inputAddr base a := by unfold memAddr inputAddr; omega
  have start : view B base p = initialStore := by
    apply Store.ext
    · funext r; exact (empty_registers pre r).1
    · funext r; exact (empty_registers pre r).2
    · funext r
      exact (off _ (even r)).1.trans (h.emptySpace zero _ (by change base ≤ memAddr base r; unfold memAddr; omega)).1
    · funext r
      exact (off _ (even r)).2.trans (h.emptySpace zero _ (by change base ≤ memAddr base r; unfold memAddr; omega)).2
  obtain ⟨old,c,he,lh,cc⟩ := tree_run I hk ε hε hε1
  have hi : 224 < B := bank_high k
  obtain ⟨t,b,hr,vt,frame,bc⟩ := program_run he B base hi input p start region
  have mem (u : ℕ) (hu : u < base) : t.nm u = s.nm u ∧ t.rm u = s.rm u := by
    have hh := frame.memory u (fun j => by unfold memAddr; omega)
    have gg := off u (fun j => by unfold inputAddr; omega)
    exact ⟨hh.1.trans gg.1,hh.2.trans gg.2⟩
  have bound : targetSlot k I.graph.n ≤ base := le_trans (slot_before_call I ε _) (show PrepareRAM.privateBase I ε ≤ base by unfold base keyBase; omega)
  have low (u : ℕ) (hu : u < 8+k) := mem u (by unfold targetSlot at bound; omega)
  have objs : Objects I ε t := by
    refine ⟨header_protected I ε s t h.hardware.header low,⟨((low 5 (by omega)).1).trans h.hardware.calls.count,?_⟩,?_,?_⟩
    · intro j A ha; simp [calls] at ha
    · intro j hj; omega
    · intro j v hj
      have hlen := (List.getElem?_eq_some_iff.mp hj).1
      have nv := ParentQuery.incident_length_le_n I
      exact ((mem _ (by unfold base keyBase; omega)).1).trans (h.hardware.graph.vertices.value j v hj)
  have reg (r : ℕ) (har : r = 142 ∨ r = 143) : t.nr r = s.nr r := by
    have hx : x.nr r = s.nr r := by rcases har with rfl|rfl <;> rfl
    exact (frame.nr _ (by omega) (by omega)).trans ((hp.nat_frame _ (pack_active_registers _ _ har)).trans hx)
  have vr (u : ℕ) : t.rr (B+u) = old.rr u := congrArg (fun z : Store => z.rr u) vt
  have vn (u : ℕ) : t.nm (memAddr base u) = old.nm u := congrArg (fun z : Store => z.nm u) vt
  have vm (u : ℕ) : t.rm (memAddr base u) = old.rm u := congrArg (fun z : Store => z.rm u) vt
  have tree : TreeView I ε t := by
    refine ⟨?_,?_⟩
    · intro v hv; change LabelRep _ (t.rr (B+281)) (t.rm (memAddr base _)); rw [vr,vm]; exact lh.labels v hv
    · intro v hv; change t.nm (memAddr base _) = _; rw [vn]; exact lh.parents v hv
  refine ⟨t,m+b,Run.seq hp hr,⟨objs,tree,(frame.nr 189 (by omega) (by decide)).trans region.work,
    (reg _ (Or.inl rfl)).trans h.hardware.graph.vertices.array_reg,(reg _ (Or.inr rfl)).trans h.hardware.graph.vertices.count_reg,?_⟩,by omega⟩
  intro v hv _
  have st : targetSlot k v < targetSlot k I.graph.n := by unfold targetSlot; omega
  exact ((mem _ (by omega)).1).trans (h.targets _ (by unfold targetSlot; omega) (st.trans_le (slot_before_call I ε 0))).1

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured Mission.TargetRecords SeparatedRAM LayerRAM SelectionRAM

def readLabel (k : ℕ) : List Atom :=
  [⟨.natOp .add 86 142 208,trivial⟩,⟨.loadNat 212 86,trivial⟩,⟨.natOp .add 88 212 212,trivial⟩,⟨.natOp .add 88 88 88,trivial⟩,
   ⟨.natConst 214 (32+2*k),trivial⟩,⟨.natOp .add 214 214 88,trivial⟩,⟨.natConst 86 19,trivial⟩,
   ⟨.natOp .add 86 86 88,trivial⟩,⟨.natOp .add 86 86 86,trivial⟩,⟨.natOp .add 86 189 86,trivial⟩,
   ⟨.loadNat 211 86,trivial⟩,⟨.loadReal 90 86,trivial⟩,⟨.natConst 210 0,trivial⟩]
def chooseLabel (b : ℕ) := Cmd.branch (.nat .eq 212 209)
  (.atoms [⟨.natConst 210 1,trivial⟩,⟨.realConst 90 0,trivial⟩])
  (.branch (.real .lt 90 (b+281)) (.atom ⟨.natConst 210 2,trivial⟩) .skip)
def writeLabel : List Atom :=
  [⟨.storeNat 214 210,trivial⟩,⟨.storeReal 214 90,trivial⟩,⟨.natConst 86 2,trivial⟩,
   ⟨.natOp .add 86 214 86,trivial⟩,⟨.storeNat 86 211,trivial⟩,⟨.natOp .add 208 208 31,trivial⟩]
def ordinaryVertex (k : ℕ) := Cmd.seq (.atoms (readLabel k)) (.seq (chooseLabel (bank k)) (.atoms writeLabel))

theorem choose_label_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hz : hasPositiveBudget I = false)
    (v b : ℕ) (input : RAMInput) (s : Store) (hv : s.nr 212 = v) (hs : s.nr 209 = I.source) (blank : s.nr 210 = 0)
    (lab : LabelRep (shortestTree I v).distance (s.rr (b+281)) (s.rr 90)) :
    ∃ t n, Run input (chooseLabel b) s t n ∧ Result I ε v t ∧ n ≤ 4 := by
  by_cases src : v = I.source
  · have g : (Guard.nat .eq 212 209).eval s = true := by simp [Guard.eval,natTest,hv,hs,src]
    let ops : List Atom := [⟨.natConst 210 1,trivial⟩,⟨.realConst 90 0,trivial⟩]
    refine ⟨_,4,Run.branchTrue g (run_atoms input ops s),⟨?_,?_,?_⟩,le_rfl⟩
    · simp [ops,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,selectedBranch,src,outputTag]
    · intro d hd; simpa [ops,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,selectedDistance,selectedBranch,src] using hd
    · intro r hr; simp [selectedBranch,src] at hr
  · have g : (Guard.nat .eq 212 209).eval s = false := by simp [Guard.eval,natTest,hv,hs,src]
    cases hd : (shortestTree I v).distance with
    | none =>
      have neg : ¬ s.rr 90 < s.rr (b+281) := by simpa only [lab.finite_iff,hd,Option.isSome_none,Bool.false_eq_true,not_false_eq_true]
      have gf : (Guard.real .lt 90 (b+281)).eval s = false := by simp [Guard.eval,realTest,neg]
      have br : selectedBranch I ε v = .absent := by simp [selectedBranch,src,hz,hd]
      exact ⟨s,_,Run.branchFalse g (Run.branchFalse gf (Run.skip s)),⟨by simpa [br,outputTag] using blank,
        fun d hh => by simp [selectedDistance,br] at hh,fun j hj => by simp [br] at hj⟩,by decide⟩
    | some d =>
      have less : s.rr 90 < s.rr (b+281) := lab.finite_iff.mpr (by simp [hd])
      have gf : (Guard.real .lt 90 (b+281)).eval s = true := by simp [Guard.eval,realTest,less]
      have br : selectedBranch I ε v = .ordinary := by simp [selectedBranch,src,hz,hd]
      let a : Atom := ⟨.natConst 210 2,trivial⟩
      refine ⟨_,_,Run.branchFalse g (Run.branchTrue gf (Run.atom a s)),⟨?_,?_,?_⟩,by decide⟩
      · simp [br,outputTag,a,Atom.eval,Store.at,Store.ofRAM,ramStep]
      · intro x hx
        have eq : d = x := by simpa [selectedDistance,br,hd] using hx
        change s.rr 90 = x
        simpa only [hd,Option.getD_some,eq] using lab.1
      · intro j hj; simp [br] at hj

def Record {k : ℕ} (I : MultiInstance k) (ε : ℝ) (v : ℕ) (s : Store) : Prop :=
  TargetRecord I ε v s ∧ s.nm (targetSlot k v+2) = ((shortestTree I v).parent.map (·+1)).getD 0
def SlotFrame (k v : ℕ) (s t : Store) : Prop := ∀ x, x < targetSlot k v ∨ targetSlot k v+3 ≤ x → t.nm x = s.nm x ∧ t.rm x = s.rm x

theorem write_label_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hz : hasPositiveBudget I = false) (v : ℕ) (input : RAMInput) (s : Store)
    (h : Result I ε v s) (addr : s.nr 214 = targetSlot k v) (par : s.nr 211 = ((shortestTree I v).parent.map (·+1)).getD 0)
    (one : s.nr 31 = 1) :
    let t := evalAtoms input writeLabel s
    Record I ε v t ∧ t.nr 208 = s.nr 208 + 1 ∧ SlotFrame k v s t := by
  let t := evalAtoms input writeLabel s
  let a := targetSlot k v
  have natM : t.nm = Function.update (Function.update s.nm a (s.nr 210)) (a+2) (s.nr 211) := by
    simp [t,a,writeLabel,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,evalNat,addr]
  have realM : t.rm = Function.update s.rm a (s.rr 90) := by
    simp [t,a,writeLabel,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,addr]
  refine ⟨⟨⟨?_,?_,?_⟩,?_⟩,?_,?_⟩
  · change t.nm a = _; simpa only [natM,Function.update_of_ne (show a ≠ a+2 by omega),Function.update_self] using h.1
  · intro d hd; change t.rm a = _; simpa only [realM,Function.update_self] using h.2.1 d hd
  · intro r hr
    obtain ⟨A,ha,_⟩ := selectedBranch_table_accepts I ε v r hr
    simp [outerCalls,hz] at ha
  · change t.nm (a+2) = _; simpa only [natM,Function.update_self] using par
  · simp [writeLabel,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,evalNat,one]
  · intro x hx; change x < a ∨ a+3 ≤ x at hx
    change t.nm x = _ ∧ t.rm x = _
    simp [natM,realM,Function.update_of_ne (show x ≠ a by omega),Function.update_of_ne (show x ≠ a+2 by omega)]

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured Mission.TargetRecords SeparatedRAM LayerRAM SelectionRAM

theorem TreeOutput.slot {k : ℕ} {I : MultiInstance k} {ε : ℝ} {s t : Store} (h : TreeOutput I ε s) (v : ℕ) (hv : v ∈ incidentVertices I)
    (frame : SlotFrame k v s t) (nr : ∀ a, a ∈ [142,143,189] → t.nr a = s.nr a) (rr : t.rr (bank k+281) = s.rr (bank k+281)) :
    TreeOutput I ε t := by
  have valid := incident_valid I v hv
  have outside : Outside I s t := by
    intro x hx; apply frame
    unfold targetSlot at *; omega
  have bound : targetSlot k I.graph.n ≤ keyBase I ε := le_trans (slot_before_call I ε _)
    (show PrepareRAM.privateBase I ε ≤ keyBase I ε by unfold keyBase; omega)
  have high (w : ℕ) := outside (memAddr (keyBase I ε) (targetAddress w+3)) (Or.inr (by unfold memAddr; omega))
  refine ⟨h.objects.frame outside,⟨?_,?_⟩,(nr _ (by decide)).trans h.keys,(nr _ (by decide)).trans h.array,(nr _ (by decide)).trans h.size,?_⟩
  · intro w hw; rw [rr,(high w).2]; exact h.tree.labels w hw
  · intro w hw; exact (high w).1.trans (h.tree.parents w hw)
  · intro w hw hin
    have ne : w ≠ v := fun eq => hin (eq ▸ hv)
    exact (frame _ (by unfold targetSlot; omega)).1.trans (h.isolated w hw hin)

theorem Record.frame {k : ℕ} {I : MultiInstance k} {ε : ℝ} {s t : Store} {v w : ℕ} (h : Record I ε w s)
    (ne : w ≠ v) (f : SlotFrame k v s t) : Record I ε w t := by
  have hh (a : ℕ) (ha : a ≤ 2) := f (targetSlot k w+a) (by unfold targetSlot; omega)
  have z := hh 0 (by decide); simp only [Nat.add_zero] at z
  exact ⟨⟨z.1.trans h.1.1,fun d hd => z.2.trans (h.1.2.1 d hd),fun r hr => (hh 1 (by decide)).1.trans (h.1.2.2 r hr)⟩,
    (hh 2 (by decide)).1.trans h.2⟩

structure RecordState {k : ℕ} (I : MultiInstance k) (ε : ℝ) (j : ℕ) (s : Store) : Prop where
  image : TreeOutput I ε s
  one : s.nr 31 = 1
  source : s.nr 209 = I.source
  index : s.nr 208 = j
  done : ∀ i < j, ∀ v, (incidentVertices I)[i]? = some v → Record I ε v s

theorem ordinary_vertex_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hz : hasPositiveBudget I = false)
    (j : ℕ) (hj : j < (incidentVertices I).length) (input : RAMInput) (s : Store) (h : RecordState I ε j s) :
    ∃ t n, Run input (ordinaryVertex k) s t n ∧ RecordState I ε (j+1) t ∧ n ≤ 23 := by
  let v := (incidentVertices I)[j]
  have hh : (incidentVertices I)[j]? = some v := List.getElem?_eq_getElem hj
  have hv := List.mem_of_getElem? hh
  let p := evalAtoms input (readLabel k) s
  let addr := memAddr (keyBase I ε) (targetAddress v+3)
  have read : s.nm (s.nr 142+s.nr 208) = v := by rw [h.image.array,h.index]; exact h.image.objects.active j v hh
  have ad : keyBase I ε + (19+(v+v+(v+v))+(19+(v+v+(v+v)))) = addr := by unfold addr memAddr targetAddress; omega
  have pf : p.nr 212 = v ∧ p.nr 214 = targetSlot k v ∧ p.rr 90 = s.rm addr ∧ p.nr 211 = s.nm addr := by
    simp [p,readLabel,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,evalNat,read,h.image.keys,ad,targetSlot]; omega
  have sent : p.rr (bank k+281) = s.rr (bank k+281) := by
    simp [p,readLabel,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,Function.update_of_ne (show bank k+281 ≠ 90 by omega)]
  have lab : LabelRep (shortestTree I v).distance (p.rr (bank k+281)) (p.rr 90) := by rw [sent,pf.2.2.1]; exact h.image.tree.labels v hv
  obtain ⟨u,c,hu,us,hc⟩ := choose_label_run I ε hz v (bank k) input p pf.1 h.source rfl lab
  have untouched (a : ℕ) (hn : a ≠ 210) : u.nr a = p.nr a := hu.nat_frame a (by
    simp [chooseLabel,Cmd.atoms,Cmd.natWrites,Atom.natWrites,hn])
  have par := h.image.tree.parents v hv
  have fin := write_label_run I ε hz v input u us ((untouched 214 (by decide)).trans pf.2.1)
    ((untouched 211 (by decide)).trans (pf.2.2.2.trans par)) ((untouched 31 (by decide)).trans h.one)
  let t := evalAtoms input writeLabel u
  have run : Run input (ordinaryVertex k) s t (13+(c+6)) := Run.seq (run_atoms _ _ _) (Run.seq hu (run_atoms _ _ _))
  have uN : u.nm = s.nm := hu.natMemory_frame rfl
  have uR : u.rm = s.rm := hu.realMemory_frame rfl
  have frame : SlotFrame k v s t := fun x hx => ⟨(fin.2.2 x hx).1.trans (congrFun uN x),(fin.2.2 x hx).2.trans (congrFun uR x)⟩
  have regs (a : ℕ) (ha : a ∈ [31,142,143,189,209]) : t.nr a = s.nr a := run.nat_frame a (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp [ordinaryVertex,readLabel,chooseLabel,writeLabel,Cmd.atoms,Cmd.natWrites,Atom.natWrites];omega)
  have sr : t.rr (bank k+281) = s.rr (bank k+281) := run.real_frame _ (by
    simp [ordinaryVertex,readLabel,chooseLabel,writeLabel,Cmd.atoms,Cmd.realWrites,Atom.realWrites])
  refine ⟨t,_,run,⟨h.image.slot v hv frame (fun a ha => regs a (by simp at ha ⊢; tauto)) sr,(regs _ (by decide)).trans h.one,
    (regs _ (by decide)).trans h.source,fin.2.1.trans (congrArg (·+1) ((untouched 208 (by decide)).trans h.index)),?_⟩,by omega⟩
  intro i hi w hw
  by_cases eq : w = v
  · exact eq ▸ fin.1
  · have hij : i ≠ j := by intro e; subst i; exact eq (Option.some.inj (hw.symm.trans hh))
    exact (h.done i (by omega) w hw).frame eq frame

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open Mission.Structured SeparatedRAM LayerRAM SelectionRAM

def ordinaryLoop (k : ℕ) := Cmd.loop (.nat .lt 208 143) (ordinaryVertex k)
def beginRecords : List Atom := [⟨.natConst 31 1,trivial⟩,⟨.loadNat 209 31,trivial⟩,⟨.natConst 208 0,trivial⟩]
def ordinaryTargets (k : ℕ) := Cmd.seq (.atoms beginRecords) (ordinaryLoop k)
def ordinary (k : ℕ) := Cmd.seq (ordinaryTree k) (ordinaryTargets k)

theorem ordinary_loop_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hz : hasPositiveBudget I = false)
    (remaining j : ℕ) (input : RAMInput) (s : Store) (hend : j+remaining = (incidentVertices I).length) (h : RecordState I ε j s) :
    ∃ t n, Run input (ordinaryLoop k) s t n ∧ RecordState I ε (incidentVertices I).length t ∧ n ≤ 25*remaining+1 := by
  induction remaining generalizing j s with
  | zero =>
    rw [Nat.add_zero] at hend
    exact ⟨s,1,Run.loopFalse (by simp [Guard.eval,natTest,h.index,h.image.size,hend]),hend ▸ h,by simp⟩
  | succ l ih =>
    have lt : j < (incidentVertices I).length := by omega
    have g : (Guard.nat .lt 208 143).eval s = true := by simp [Guard.eval,natTest,h.index,h.image.size,lt]
    obtain ⟨p,c,hr,ph,hc⟩ := ordinary_vertex_run I ε hz j lt input s h
    obtain ⟨t,b,he,th,hb⟩ := ih (j+1) p (by omega) ph
    refine ⟨t,_,Run.loopTrue g hr he,th,?_⟩
    omega

theorem ordinary_encoding {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hz : hasPositiveBudget I = false)
    (s : Store) (h : RecordState I ε (incidentVertices I).length s) : EncodesMultiOutput I ε (s.at 0) := by
  have record (v : ℕ) (hv : v ∈ incidentVertices I) := h.done _ (List.idxOf_lt_length_of_mem hv) v (List.getElem?_idxOf hv)
  apply encoding_of_records I ε hε s h.image.objects _ (fun _ v hv => (record v hv).2)
  intro v hv
  by_cases hm : v ∈ incidentVertices I
  · exact (record v hm).1
  · have hs : v ≠ I.source := fun he => hm (he ▸ incident_source_mem I)
    have br : selectedBranch I ε v = .absent := by simp [selectedBranch,hs,hz,inactive_distance I v hm]
    exact ⟨by simpa [br,outputTag] using h.image.isolated v hv hm,
      fun d hd => by simp [selectedDistance,br] at hd,fun j hj => by simp [br] at hj⟩

theorem ordinary_targets_run {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hz : hasPositiveBudget I = false)
    (input : RAMInput) (s : Store) (h : TreeOutput I ε s) :
    ∃ t n, Run input (ordinaryTargets k) s t n ∧ EncodesMultiOutput I ε (t.at 0) ∧ n ≤ 25*(incidentVertices I).length+4 := by
  let p := evalAtoms input beginRecords s
  have src : p.nr 209 = I.source := h.objects.header.1.2.1
  have init : RecordState I ε 0 p :=
    ⟨⟨h.objects.frame (fun _ _ => ⟨rfl,rfl⟩),⟨h.tree.labels,h.tree.parents⟩,h.keys,h.array,h.size,h.isolated⟩,rfl,src,rfl,by intro i hi; omega⟩
  obtain ⟨t,c,hr,th,hc⟩ := ordinary_loop_run I ε hz (incidentVertices I).length 0 input p (by omega) init
  exact ⟨t,3+c,Run.seq (run_atoms _ _ _) hr,ordinary_encoding I ε hε hz t th,by omega⟩

noncomputable def ordinaryCost {k : ℕ} (I : MultiInstance k) (ε : ℝ) :=
  (8*k+22)*I.graph.edges.length + 3*oldCost I ε + 25*(incidentVertices I).length + 23

theorem ordinary_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hz : hasPositiveBudget I = false) (s : Store) (im : TableOutput I ε s) (a : ℕ) (pre : Run (multiInput I ε) (constructAll k) initialStore s a) :
    ∃ t n, Run (multiInput I ε) (ordinary k) (evalAtoms (multiInput I ε) modeOps s) t n ∧
      EncodesMultiOutput I ε (t.at 0) ∧ n ≤ ordinaryCost I ε := by
  obtain ⟨p,c,hr,hp,hc⟩ := tree_image_run I hk ε hε hε1 hz s im a pre
  obtain ⟨t,b,ht,oh,hb⟩ := ordinary_targets_run I ε hε hz (multiInput I ε) p hp
  exact ⟨t,c+b,Run.seq hr ht,oh,by unfold ordinaryCost; omega⟩

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace NearLinearRSP.TwoResources.Supplement.OrdinaryRAM
open LayerRAM

theorem graph_work {k : ℕ} (I : MultiInstance k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((max 1 I.graph.edges.length : ℕ):ℝ) * (1+Real.log (max 2 I.graph.n : ℕ)) ≤ multiScale I ε := by
  let N : ℝ := (max 2 I.graph.n : ℕ)
  let M : ℝ := (max 1 I.graph.edges.length : ℕ)
  let H := 1+Real.log N
  have n1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ max 2 I.graph.n by omega)
  have hn := Real.log_nonneg n1
  have hm : 0 ≤ M*H := by dsimp [M,H]; positivity
  have prod : 1 ≤ N*aspectRatio (lengthInstance I) := one_le_mul_of_one_le_of_one_le n1 (one_le_aspectRatio _)
  have logP := Real.log_nonneg prod
  have hl : 1 ≤ 1+Real.log (N*aspectRatio (lengthInstance I)) := by linarith
  change M*H ≤ M*H*(1+Real.log (N*aspectRatio (lengthInstance I))) / ε^(4*k+1)
  apply (le_div_iff₀ (pow_pos hε _)).mpr
  exact (mul_le_of_le_one_right hm (pow_le_one₀ hε.le hε1.le)).trans (le_mul_of_one_le_right hm hl)

theorem old_count {k : ℕ} (I : MultiInstance k) (ε : ℝ) :
    oldCost I ε ≤ 18*multiQ k ε+14*(Nat.log 2 I.graph.n+1)^2+
      1000*(max 1 I.graph.edges.length)*(Nat.clog 2 (2*capacity I)+1)+200 := by
  let M := max 1 I.graph.edges.length
  let V := (incidentVertices I).length
  let D := Nat.clog 2 (2*capacity I)+1
  have m : I.graph.edges.length ≤ M := Nat.le_max_right _ _
  have m1 : 1 ≤ M := Nat.le_max_left _ _
  have v : V ≤ 3*M := by have hh := incident_length_bound I; change V ≤ 1+2*I.graph.edges.length at hh; omega
  have c : capacity I ≤ 6*M := by have hh := capacity_le_twice I; change capacity I ≤ 2*V at hh; omega
  have hr : height I ≤ D := by dsimp [D]; rw [tournament_depth]; omega
  have d : 1 ≤ D := by dsimp [D]; omega
  have md := Nat.mul_le_mul_left M d
  have dm := Nat.mul_le_mul_right D m1
  have sv : (38*Nat.clog 2 (2*capacity I)+58)*V ≤ (38*D+58)*(3*M) := by
    gcongr; dsimp [D]; omega
  have sm : (19*Nat.clog 2 (2*capacity I)+46)*I.graph.edges.length ≤ (19*D+46)*M := by
    gcongr; dsimp [D];omega
  unfold oldCost
  change _ ≤ 18*multiQ k ε + 14*(Nat.log 2 I.graph.n+1)^2 + 1000*M*D+200
  change (38*Nat.clog 2 (2*capacity I)+58)*(incidentVertices I).length ≤ _ at sv
  nlinarith only [sv,sm,hr,c,m,md,dm,m1,d]

noncomputable def coefficient (k : ℕ) : ℝ :=
  8*(k:ℝ)+22 + 3*(18*(8192*(k:ℝ)+2)+14*PrepareRAM.logFactor^2+1000*heightFactor+200)+75+23

theorem ordinary_bound {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (ordinaryCost I ε : ℝ) ≤ coefficient k * multiScale I ε := by
  let M : ℝ := (max 1 I.graph.edges.length : ℕ)
  let V : ℝ := (incidentVertices I).length
  let D : ℝ := (Nat.clog 2 (2*capacity I)+1 : ℕ)
  let H := 1+Real.log (max 2 I.graph.n : ℕ)
  let S := multiScale I ε
  have one : 1 ≤ S := SpaceRAM.scale_one I hk ε hε hε1
  have m : (I.graph.edges.length:ℝ) ≤ S := (PrepareRAM.graph_scales I ε hε hε1).1
  have maxLe : M ≤ S := by simpa [M,Nat.cast_max] using max_le one m
  have vertices : V ≤ 3*M := by
    have hi := incident_length_bound I
    dsimp only [V,M]; exact_mod_cast (show (incidentVertices I).length ≤ 3*max 1 I.graph.edges.length by omega)
  have hsq : H^2 ≤ S := (PrepareRAM.graph_scales I ε hε hε1).2
  have L := (PrepareRAM.binary_log I).trans (mul_le_mul_of_nonneg_left hsq (sq_nonneg PrepareRAM.logFactor))
  have hg := multiQ_bound k ε hε hε1
  rw [Nat.cast_add,Nat.cast_one] at hg
  have q : (multiQ k ε:ℝ) ≤ (8192*(k:ℝ)+2)*S := by
    calc
      _ ≤ (8192*(k:ℝ)+2) / ε^2 := by linarith only [hg]
      _ = (8192*(k:ℝ)+2)*(1/ε^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (multiScale_lower I hk ε hε hε1) (by positivity)
  have GW : M*H ≤ S := graph_work I ε hε hε1
  have d : D ≤ heightFactor*H := depth_bound I
  have md : M*D ≤ heightFactor*S := calc
    _ ≤ M*(heightFactor*H) := mul_le_mul_of_nonneg_left d (by dsimp [M]; positivity)
    _ = heightFactor*(M*H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left GW height_factor_pos.le
  have old : (oldCost I ε : ℝ) ≤ 18*(multiQ k ε:ℝ)+14*((Nat.log 2 I.graph.n:ℝ)+1)^2+1000*M*D+200 := by
    dsimp only [M,D]; exact_mod_cast old_count I ε
  have base := mul_le_mul_of_nonneg_left m (show 0 ≤ 8*(k:ℝ)+22 by positivity)
  unfold ordinaryCost coefficient
  push_cast
  change (8*(k:ℝ)+22)*(I.graph.edges.length:ℝ)+3*(oldCost I ε:ℝ)+25*V+23 ≤ _*S
  linarith only [base,old,q,L,md,vertices,maxLe,one]

end NearLinearRSP.TwoResources.Supplement.OrdinaryRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement
open Mission.Structured

def PreprocessingRealization : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ build : Cmd, ∃ B : ℝ, 0 < B ∧
    ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s n, Run (multiInput I ε) build initialStore s n ∧
        (n : ℝ) ≤ B * multiScale I ε ∧ EncodesMultiOutput I ε (s.at 0)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.CompleteRAM
open Mission.Structured LayerRAM

def build (k : ℕ) := Cmd.seq (constructAll k) (.seq (.atoms OrdinaryRAM.modeOps) (.branch (.nat .lt 30 86) (SelectionRAM.positive k) (OrdinaryRAM.ordinary k)))
noncomputable def buildCoefficient (k : ℕ) : ℝ := |tableCoefficient k| + |SelectionRAM.coefficient k| + |OrdinaryRAM.coefficient k| + 5

theorem coefficient_pos (k : ℕ) : 0 < buildCoefficient k := by unfold buildCoefficient; positivity

theorem build_run {k : ℕ} (I : MultiInstance k) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ t n, Run (multiInput I ε) (build k) initialStore t n ∧ (n:ℝ) ≤ buildCoefficient k * multiScale I ε ∧ EncodesMultiOutput I ε (t.at 0) := by
  let input := multiInput I ε
  obtain ⟨s,a,hr,h,ha⟩ := construct_all_bound I hk ε hε hε1
  let x := evalAtoms input OrdinaryRAM.modeOps s
  have hx : Run input (.atoms OrdinaryRAM.modeOps) s x 3 := run_atoms input _ _
  have count : x.nr 86 = (outerCalls I ε).length := h.hardware.calls.count
  have zero : x.nr 30 = 0 := rfl
  have one := SpaceRAM.scale_one I hk ε hε hε1
  have pos : 0 ≤ multiScale I ε := by linarith only [one]
  have ha' := ha.trans (mul_le_mul_of_nonneg_right (le_abs_self _) pos)
  cases hp : hasPositiveBudget I with
  | false =>
    have g : (Guard.nat .lt 30 86).eval x = false := by simp [Guard.eval,natTest,zero,count,outerCalls,hp]
    obtain ⟨t,b,hb,enc,hc⟩ := OrdinaryRAM.ordinary_run I hk ε hε hε1 hp s h a hr
    have cost := (show (b:ℝ) ≤ _ by exact_mod_cast hc).trans (OrdinaryRAM.ordinary_bound I hk ε hε hε1)
    have cost' := cost.trans (mul_le_mul_of_nonneg_right (le_abs_self _) pos)
    have other := mul_nonneg (abs_nonneg (SelectionRAM.coefficient k)) pos
    refine ⟨t,a+(3+(1+b)),Run.seq hr (Run.seq hx (Run.branchFalse g hb)),?_,enc⟩
    unfold buildCoefficient; push_cast; linarith only [ha',cost',other,one]
  | true =>
    have g : (Guard.nat .lt 30 86).eval x = true := by simp [Guard.eval,natTest,zero,count,outerCalls,hp]
    have xh : TableOutput I ε x := ⟨h.hardware.copy (fun a ha _ => by
      simp [x,OrdinaryRAM.modeOps,evalAtoms,Atom.eval,Store.at,Store.ofRAM,ramStep,
        Function.update_of_ne (show a ≠ 30 by omega),Function.update_of_ne (show a ≠ 86 by omega)]) rfl rfl,
      fun j hj A ha => (h.tables j hj A ha).frame (fun _ _ => ⟨rfl,rfl⟩),h.targets,h.emptySpace⟩
    obtain ⟨t,b,hb,enc,hc⟩ := SelectionRAM.positive_run I hk ε hε hp x xh
    have cost := (show (b:ℝ) ≤ _ by exact_mod_cast hc).trans (SelectionRAM.positive_bound I hk ε hε hε1)
    have cost' := cost.trans (mul_le_mul_of_nonneg_right (le_abs_self _) pos)
    have other := mul_nonneg (abs_nonneg (OrdinaryRAM.coefficient k)) pos
    refine ⟨t,a+(3+(1+b+1)),Run.seq hr (Run.seq hx (Run.branchTrue g hb)),?_,enc⟩
    unfold buildCoefficient; push_cast; linarith only [ha',cost',other,one]

theorem preprocessing : PreprocessingRealization :=
  fun k hk => ⟨build k,buildCoefficient k,coefficient_pos k,fun I ε hε hε1 => build_run I (by omega) ε hε hε1⟩

end NearLinearRSP.TwoResources.Supplement.CompleteRAM

end

open NearLinearRSP.TwoResources NearLinearRSP.TwoResources.Supplement
open NearLinearRSP.TwoResources.Mission.Structured

theorem solution :
  ∀ k : ℕ, 2 ≤ k → ∃ build : Cmd, ∃ B : ℝ, 0 < B ∧
    ∀ (I : MultiInstance k) (ε : ℝ), 0 < ε → ε < 1 →
      ∃ s n, Run (multiInput I ε) build initialStore s n ∧
        (n : ℝ) ≤ B * multiScale I ε ∧ EncodesMultiOutput I ε (s.at 0) :=
  CompleteRAM.preprocessing
