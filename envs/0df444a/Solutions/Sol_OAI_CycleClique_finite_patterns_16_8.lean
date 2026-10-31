-- Prove2me | solution 1 for OAI.CycleClique.finite_patterns_16_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T20:41:32.017372+00:00
-- url     : https://prove2.me/submissions/8de6088e-b92a-4160-acfe-7292f0756e57

import Mathlib
import Definitions.Def_OAIQ107D130
import Definitions.Def_OAIQ107D133
import Theorems.Thm_OAI_CycleClique_patterns_16_8_0_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_10_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_11_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_12_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_13_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_14_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_15_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_16_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_17_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_18_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_19_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_1_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_20_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_21_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_22_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_25_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_26_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_27_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_28_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_2_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_3_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_4_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_5_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_6_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_7_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_8_verified
import Theorems.Thm_OAI_CycleClique_patterns_16_8_9_verified

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates067
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2120_checked : certificate_2120.Valid 16 8 16 certificate_2120_q certificate_2120_edges 8 4 [] := by decide +kernel
theorem certificate_2120_valid : certificate_2120.Valid 16 8 (patternOrder [[1],[1],[1],[5]]) (patternClique [[1],[1],[1],[5]]) (patternEdges [[1],[1],[1],[5]]) (patternAmount [[1],[1],[1],[5]]) (patternEdgeCount [[1],[1],[1],[5]]) [] := certificate_2120_checked

theorem certificate_2121_checked : certificate_2121.Valid 16 8 13 certificate_2121_q certificate_2121_edges 5 5 [] := by decide +kernel
theorem certificate_2121_valid : certificate_2121.Valid 16 8 (patternOrder [[1],[1],[1,1,1]]) (patternClique [[1],[1],[1,1,1]]) (patternEdges [[1],[1],[1,1,1]]) (patternAmount [[1],[1],[1,1,1]]) (patternEdgeCount [[1],[1],[1,1,1]]) [] := certificate_2121_checked

theorem certificate_2122_checked : certificate_2122.Valid 16 8 14 certificate_2122_q certificate_2122_edges 6 5 [] := by decide +kernel
theorem certificate_2122_valid : certificate_2122.Valid 16 8 (patternOrder [[1],[1],[1,1,2]]) (patternClique [[1],[1],[1,1,2]]) (patternEdges [[1],[1],[1,1,2]]) (patternAmount [[1],[1],[1,1,2]]) (patternEdgeCount [[1],[1],[1,1,2]]) [] := certificate_2122_checked

theorem certificate_2123_checked : certificate_2123.Valid 16 8 15 certificate_2123_q certificate_2123_edges 7 5 [] := by decide +kernel
theorem certificate_2123_valid : certificate_2123.Valid 16 8 (patternOrder [[1],[1],[1,1,3]]) (patternClique [[1],[1],[1,1,3]]) (patternEdges [[1],[1],[1,1,3]]) (patternAmount [[1],[1],[1,1,3]]) (patternEdgeCount [[1],[1],[1,1,3]]) [] := certificate_2123_checked

theorem certificate_2124_checked : certificate_2124.Valid 16 8 16 certificate_2124_q certificate_2124_edges 8 5 [] := by decide +kernel
theorem certificate_2124_valid : certificate_2124.Valid 16 8 (patternOrder [[1],[1],[1,1,4]]) (patternClique [[1],[1],[1,1,4]]) (patternEdges [[1],[1],[1,1,4]]) (patternAmount [[1],[1],[1,1,4]]) (patternEdgeCount [[1],[1],[1,1,4]]) [] := certificate_2124_checked

theorem certificate_2125_checked : certificate_2125.Valid 16 8 14 certificate_2125_q certificate_2125_edges 6 5 [] := by decide +kernel
theorem certificate_2125_valid : certificate_2125.Valid 16 8 (patternOrder [[1],[1],[1,2,1]]) (patternClique [[1],[1],[1,2,1]]) (patternEdges [[1],[1],[1,2,1]]) (patternAmount [[1],[1],[1,2,1]]) (patternEdgeCount [[1],[1],[1,2,1]]) [] := certificate_2125_checked

theorem certificate_2126_checked : certificate_2126.Valid 16 8 15 certificate_2126_q certificate_2126_edges 7 5 [] := by decide +kernel
theorem certificate_2126_valid : certificate_2126.Valid 16 8 (patternOrder [[1],[1],[1,2,2]]) (patternClique [[1],[1],[1,2,2]]) (patternEdges [[1],[1],[1,2,2]]) (patternAmount [[1],[1],[1,2,2]]) (patternEdgeCount [[1],[1],[1,2,2]]) [] := certificate_2126_checked

theorem certificate_2127_checked : certificate_2127.Valid 16 8 16 certificate_2127_q certificate_2127_edges 8 5 [] := by decide +kernel
theorem certificate_2127_valid : certificate_2127.Valid 16 8 (patternOrder [[1],[1],[1,2,3]]) (patternClique [[1],[1],[1,2,3]]) (patternEdges [[1],[1],[1,2,3]]) (patternAmount [[1],[1],[1,2,3]]) (patternEdgeCount [[1],[1],[1,2,3]]) [] := certificate_2127_checked

theorem certificate_2128_checked : certificate_2128.Valid 16 8 15 certificate_2128_q certificate_2128_edges 7 5 [] := by decide +kernel
theorem certificate_2128_valid : certificate_2128.Valid 16 8 (patternOrder [[1],[1],[1,3,1]]) (patternClique [[1],[1],[1,3,1]]) (patternEdges [[1],[1],[1,3,1]]) (patternAmount [[1],[1],[1,3,1]]) (patternEdgeCount [[1],[1],[1,3,1]]) [] := certificate_2128_checked

theorem certificate_2129_checked : certificate_2129.Valid 16 8 16 certificate_2129_q certificate_2129_edges 8 5 [] := by decide +kernel
theorem certificate_2129_valid : certificate_2129.Valid 16 8 (patternOrder [[1],[1],[1,3,2]]) (patternClique [[1],[1],[1,3,2]]) (patternEdges [[1],[1],[1,3,2]]) (patternAmount [[1],[1],[1,3,2]]) (patternEdgeCount [[1],[1],[1,3,2]]) [] := certificate_2129_checked

theorem certificate_2130_checked : certificate_2130.Valid 16 8 16 certificate_2130_q certificate_2130_edges 8 5 [] := by decide +kernel
theorem certificate_2130_valid : certificate_2130.Valid 16 8 (patternOrder [[1],[1],[1,4,1]]) (patternClique [[1],[1],[1,4,1]]) (patternEdges [[1],[1],[1,4,1]]) (patternAmount [[1],[1],[1,4,1]]) (patternEdgeCount [[1],[1],[1,4,1]]) [] := certificate_2130_checked

theorem certificate_2131_checked : certificate_2131.Valid 16 8 14 certificate_2131_q certificate_2131_edges 6 4 [] := by decide +kernel
theorem certificate_2131_valid : certificate_2131.Valid 16 8 (patternOrder [[1],[1],[2],[2]]) (patternClique [[1],[1],[2],[2]]) (patternEdges [[1],[1],[2],[2]]) (patternAmount [[1],[1],[2],[2]]) (patternEdgeCount [[1],[1],[2],[2]]) [] := certificate_2131_checked

theorem certificate_2132_checked : certificate_2132.Valid 16 8 15 certificate_2132_q certificate_2132_edges 7 4 [] := by decide +kernel
theorem certificate_2132_valid : certificate_2132.Valid 16 8 (patternOrder [[1],[1],[2],[3]]) (patternClique [[1],[1],[2],[3]]) (patternEdges [[1],[1],[2],[3]]) (patternAmount [[1],[1],[2],[3]]) (patternEdgeCount [[1],[1],[2],[3]]) [] := certificate_2132_checked

theorem certificate_2133_checked : certificate_2133.Valid 16 8 16 certificate_2133_q certificate_2133_edges 8 4 [] := by decide +kernel
theorem certificate_2133_valid : certificate_2133.Valid 16 8 (patternOrder [[1],[1],[2],[4]]) (patternClique [[1],[1],[2],[4]]) (patternEdges [[1],[1],[2],[4]]) (patternAmount [[1],[1],[2],[4]]) (patternEdgeCount [[1],[1],[2],[4]]) [] := certificate_2133_checked

theorem certificate_2134_checked : certificate_2134.Valid 16 8 15 certificate_2134_q certificate_2134_edges 7 5 [] := by decide +kernel
theorem certificate_2134_valid : certificate_2134.Valid 16 8 (patternOrder [[1],[1],[2,1,2]]) (patternClique [[1],[1],[2,1,2]]) (patternEdges [[1],[1],[2,1,2]]) (patternAmount [[1],[1],[2,1,2]]) (patternEdgeCount [[1],[1],[2,1,2]]) [] := certificate_2134_checked

theorem certificate_2135_checked : certificate_2135.Valid 16 8 16 certificate_2135_q certificate_2135_edges 8 5 [] := by decide +kernel
theorem certificate_2135_valid : certificate_2135.Valid 16 8 (patternOrder [[1],[1],[2,1,3]]) (patternClique [[1],[1],[2,1,3]]) (patternEdges [[1],[1],[2,1,3]]) (patternAmount [[1],[1],[2,1,3]]) (patternEdgeCount [[1],[1],[2,1,3]]) [] := certificate_2135_checked

theorem certificate_2136_checked : certificate_2136.Valid 16 8 16 certificate_2136_q certificate_2136_edges 8 5 [] := by decide +kernel
theorem certificate_2136_valid : certificate_2136.Valid 16 8 (patternOrder [[1],[1],[2,2,2]]) (patternClique [[1],[1],[2,2,2]]) (patternEdges [[1],[1],[2,2,2]]) (patternAmount [[1],[1],[2,2,2]]) (patternEdgeCount [[1],[1],[2,2,2]]) [] := certificate_2136_checked

theorem certificate_2137_checked : certificate_2137.Valid 16 8 16 certificate_2137_q certificate_2137_edges 8 4 [] := by decide +kernel
theorem certificate_2137_valid : certificate_2137.Valid 16 8 (patternOrder [[1],[1],[3],[3]]) (patternClique [[1],[1],[3],[3]]) (patternEdges [[1],[1],[3],[3]]) (patternAmount [[1],[1],[3],[3]]) (patternEdgeCount [[1],[1],[3],[3]]) [] := certificate_2137_checked

theorem certificate_2138_checked : certificate_2138.Valid 16 8 13 certificate_2138_q certificate_2138_edges 5 5 [] := by decide +kernel
theorem certificate_2138_valid : certificate_2138.Valid 16 8 (patternOrder [[1],[1,1],[1,1]]) (patternClique [[1],[1,1],[1,1]]) (patternEdges [[1],[1,1],[1,1]]) (patternAmount [[1],[1,1],[1,1]]) (patternEdgeCount [[1],[1,1],[1,1]]) [] := certificate_2138_checked

theorem certificate_2139_checked : certificate_2139.Valid 16 8 14 certificate_2139_q certificate_2139_edges 6 5 [] := by decide +kernel
theorem certificate_2139_valid : certificate_2139.Valid 16 8 (patternOrder [[1],[1,1],[1,2]]) (patternClique [[1],[1,1],[1,2]]) (patternEdges [[1],[1,1],[1,2]]) (patternAmount [[1],[1,1],[1,2]]) (patternEdgeCount [[1],[1,1],[1,2]]) [] := certificate_2139_checked

theorem certificate_2140_checked : certificate_2140.Valid 16 8 15 certificate_2140_q certificate_2140_edges 7 5 [] := by decide +kernel
theorem certificate_2140_valid : certificate_2140.Valid 16 8 (patternOrder [[1],[1,1],[1,3]]) (patternClique [[1],[1,1],[1,3]]) (patternEdges [[1],[1,1],[1,3]]) (patternAmount [[1],[1,1],[1,3]]) (patternEdgeCount [[1],[1,1],[1,3]]) [] := certificate_2140_checked

theorem certificate_2141_checked : certificate_2141.Valid 16 8 16 certificate_2141_q certificate_2141_edges 8 5 [] := by decide +kernel
theorem certificate_2141_valid : certificate_2141.Valid 16 8 (patternOrder [[1],[1,1],[1,4]]) (patternClique [[1],[1,1],[1,4]]) (patternEdges [[1],[1,1],[1,4]]) (patternAmount [[1],[1,1],[1,4]]) (patternEdgeCount [[1],[1,1],[1,4]]) [] := certificate_2141_checked

theorem certificate_2142_checked : certificate_2142.Valid 16 8 15 certificate_2142_q certificate_2142_edges 7 5 [] := by decide +kernel
theorem certificate_2142_valid : certificate_2142.Valid 16 8 (patternOrder [[1],[1,1],[2,2]]) (patternClique [[1],[1,1],[2,2]]) (patternEdges [[1],[1,1],[2,2]]) (patternAmount [[1],[1,1],[2,2]]) (patternEdgeCount [[1],[1,1],[2,2]]) [] := certificate_2142_checked

theorem certificate_2143_checked : certificate_2143.Valid 16 8 16 certificate_2143_q certificate_2143_edges 8 5 [] := by decide +kernel
theorem certificate_2143_valid : certificate_2143.Valid 16 8 (patternOrder [[1],[1,1],[2,3]]) (patternClique [[1],[1,1],[2,3]]) (patternEdges [[1],[1,1],[2,3]]) (patternAmount [[1],[1,1],[2,3]]) (patternEdgeCount [[1],[1,1],[2,3]]) [] := certificate_2143_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates068
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2144_checked : certificate_2144.Valid 16 8 14 certificate_2144_q certificate_2144_edges 6 5 [] := by decide +kernel
theorem certificate_2144_valid : certificate_2144.Valid 16 8 (patternOrder [[1],[1,1,1],[2]]) (patternClique [[1],[1,1,1],[2]]) (patternEdges [[1],[1,1,1],[2]]) (patternAmount [[1],[1,1,1],[2]]) (patternEdgeCount [[1],[1,1,1],[2]]) [] := certificate_2144_checked

theorem certificate_2145_checked : certificate_2145.Valid 16 8 15 certificate_2145_q certificate_2145_edges 7 5 [] := by decide +kernel
theorem certificate_2145_valid : certificate_2145.Valid 16 8 (patternOrder [[1],[1,1,1],[3]]) (patternClique [[1],[1,1,1],[3]]) (patternEdges [[1],[1,1,1],[3]]) (patternAmount [[1],[1,1,1],[3]]) (patternEdgeCount [[1],[1,1,1],[3]]) [] := certificate_2145_checked

theorem certificate_2146_checked : certificate_2146.Valid 16 8 16 certificate_2146_q certificate_2146_edges 8 5 [] := by decide +kernel
theorem certificate_2146_valid : certificate_2146.Valid 16 8 (patternOrder [[1],[1,1,1],[4]]) (patternClique [[1],[1,1,1],[4]]) (patternEdges [[1],[1,1,1],[4]]) (patternAmount [[1],[1,1,1],[4]]) (patternEdgeCount [[1],[1,1,1],[4]]) [] := certificate_2146_checked

theorem certificate_2147_checked : certificate_2147.Valid 16 8 14 certificate_2147_q certificate_2147_edges 6 6 [] := by decide +kernel
theorem certificate_2147_valid : certificate_2147.Valid 16 8 (patternOrder [[1],[1,1,1,1,1]]) (patternClique [[1],[1,1,1,1,1]]) (patternEdges [[1],[1,1,1,1,1]]) (patternAmount [[1],[1,1,1,1,1]]) (patternEdgeCount [[1],[1,1,1,1,1]]) [] := certificate_2147_checked

theorem certificate_2148_checked : certificate_2148.Valid 16 8 15 certificate_2148_q certificate_2148_edges 7 6 [] := by decide +kernel
theorem certificate_2148_valid : certificate_2148.Valid 16 8 (patternOrder [[1],[1,1,1,1,2]]) (patternClique [[1],[1,1,1,1,2]]) (patternEdges [[1],[1,1,1,1,2]]) (patternAmount [[1],[1,1,1,1,2]]) (patternEdgeCount [[1],[1,1,1,1,2]]) [] := certificate_2148_checked

theorem certificate_2149_checked : certificate_2149.Valid 16 8 16 certificate_2149_q certificate_2149_edges 8 6 [] := by decide +kernel
theorem certificate_2149_valid : certificate_2149.Valid 16 8 (patternOrder [[1],[1,1,1,1,3]]) (patternClique [[1],[1,1,1,1,3]]) (patternEdges [[1],[1,1,1,1,3]]) (patternAmount [[1],[1,1,1,1,3]]) (patternEdgeCount [[1],[1,1,1,1,3]]) [] := certificate_2149_checked

theorem certificate_2150_checked : certificate_2150.Valid 16 8 15 certificate_2150_q certificate_2150_edges 7 6 [] := by decide +kernel
theorem certificate_2150_valid : certificate_2150.Valid 16 8 (patternOrder [[1],[1,1,1,2,1]]) (patternClique [[1],[1,1,1,2,1]]) (patternEdges [[1],[1,1,1,2,1]]) (patternAmount [[1],[1,1,1,2,1]]) (patternEdgeCount [[1],[1,1,1,2,1]]) [] := certificate_2150_checked

theorem certificate_2151_checked : certificate_2151.Valid 16 8 16 certificate_2151_q certificate_2151_edges 8 6 [] := by decide +kernel
theorem certificate_2151_valid : certificate_2151.Valid 16 8 (patternOrder [[1],[1,1,1,2,2]]) (patternClique [[1],[1,1,1,2,2]]) (patternEdges [[1],[1,1,1,2,2]]) (patternAmount [[1],[1,1,1,2,2]]) (patternEdgeCount [[1],[1,1,1,2,2]]) [] := certificate_2151_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Certificates070
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem certificate_2216_checked : certificate_2216.Valid 16 8 16 certificate_2216_q certificate_2216_edges 8 5 [] := by decide +kernel
theorem certificate_2216_valid : certificate_2216.Valid 16 8 (patternOrder [[1,2],[1,2],[2]]) (patternClique [[1,2],[1,2],[2]]) (patternEdges [[1,2],[1,2],[2]]) (patternAmount [[1,2],[1,2],[2]]) (patternEdgeCount [[1,2],[1,2],[2]]) [] := certificate_2216_checked

theorem certificate_2217_checked : certificate_2217.Valid 16 8 16 certificate_2217_q certificate_2217_edges 8 6 [] := by decide +kernel
theorem certificate_2217_valid : certificate_2217.Valid 16 8 (patternOrder [[1,2,1],[1,2,1]]) (patternClique [[1,2,1],[1,2,1]]) (patternEdges [[1,2,1],[1,2,1]]) (patternAmount [[1,2,1],[1,2,1]]) (patternEdgeCount [[1,2,1],[1,2,1]]) [] := certificate_2217_checked

theorem certificate_2218_checked : certificate_2218.Valid 16 8 16 certificate_2218_q certificate_2218_edges 8 5 [] := by decide +kernel
theorem certificate_2218_valid : certificate_2218.Valid 16 8 (patternOrder [[1,2,1],[2],[2]]) (patternClique [[1,2,1],[2],[2]]) (patternEdges [[1,2,1],[2],[2]]) (patternAmount [[1,2,1],[2],[2]]) (patternEdgeCount [[1,2,1],[2],[2]]) [] := certificate_2218_checked

theorem certificate_2219_checked : certificate_2219.Valid 16 8 16 certificate_2219_q certificate_2219_edges 8 4 [] := by decide +kernel
theorem certificate_2219_valid : certificate_2219.Valid 16 8 (patternOrder [[2],[2],[2],[2]]) (patternClique [[2],[2],[2],[2]]) (patternEdges [[2],[2],[2],[2]]) (patternAmount [[2],[2],[2],[2]]) (patternEdgeCount [[2],[2],[2],[2]]) [] := certificate_2219_checked

end CycleClique

end OAI
end

section
-- module Solutions.OAIQ107_CC.Ramsey_CycleClique_Patterns16x8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem patterns_16_8_23_verified : ∀ D ∈ patterns_16_8_23, PatternVerified 16 8 D := by

  simp only [patterns_16_8_23, List.forall_mem_cons]

  exact ⟨⟨certificate_2120, certificate_2120_valid⟩, ⟨⟨certificate_2121, certificate_2121_valid⟩, ⟨⟨certificate_2122, certificate_2122_valid⟩, ⟨⟨certificate_2123, certificate_2123_valid⟩, ⟨⟨certificate_2124, certificate_2124_valid⟩, ⟨⟨certificate_2125, certificate_2125_valid⟩, ⟨⟨certificate_2126, certificate_2126_valid⟩, ⟨⟨certificate_2127, certificate_2127_valid⟩, ⟨⟨certificate_2128, certificate_2128_valid⟩, ⟨⟨certificate_2129, certificate_2129_valid⟩, ⟨⟨certificate_2130, certificate_2130_valid⟩, ⟨⟨certificate_2131, certificate_2131_valid⟩, ⟨⟨certificate_2132, certificate_2132_valid⟩, ⟨⟨certificate_2133, certificate_2133_valid⟩, ⟨⟨certificate_2134, certificate_2134_valid⟩, ⟨⟨certificate_2135, certificate_2135_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_16_8_24_verified : ∀ D ∈ patterns_16_8_24, PatternVerified 16 8 D := by

  simp only [patterns_16_8_24, List.forall_mem_cons]

  exact ⟨⟨certificate_2136, certificate_2136_valid⟩, ⟨⟨certificate_2137, certificate_2137_valid⟩, ⟨⟨certificate_2138, certificate_2138_valid⟩, ⟨⟨certificate_2139, certificate_2139_valid⟩, ⟨⟨certificate_2140, certificate_2140_valid⟩, ⟨⟨certificate_2141, certificate_2141_valid⟩, ⟨⟨certificate_2142, certificate_2142_valid⟩, ⟨⟨certificate_2143, certificate_2143_valid⟩, ⟨⟨certificate_2144, certificate_2144_valid⟩, ⟨⟨certificate_2145, certificate_2145_valid⟩, ⟨⟨certificate_2146, certificate_2146_valid⟩, ⟨⟨certificate_2147, certificate_2147_valid⟩, ⟨⟨certificate_2148, certificate_2148_valid⟩, ⟨⟨certificate_2149, certificate_2149_valid⟩, ⟨⟨certificate_2150, certificate_2150_valid⟩, ⟨⟨certificate_2151, certificate_2151_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_16_8_29_verified : ∀ D ∈ patterns_16_8_29, PatternVerified 16 8 D := by

  simp only [patterns_16_8_29, List.forall_mem_cons]

  exact ⟨⟨certificate_2216, certificate_2216_valid⟩, ⟨⟨certificate_2217, certificate_2217_valid⟩, ⟨⟨certificate_2218, certificate_2218_valid⟩, ⟨⟨certificate_2219, certificate_2219_valid⟩, (by simp)⟩⟩⟩⟩

theorem patterns_16_8_verified : ∀ D ∈ patterns_16_8, PatternVerified 16 8 D := by

  simp only [patterns_16_8, List.forall_mem_append]

  exact ⟨patterns_16_8_0_verified, ⟨patterns_16_8_1_verified, ⟨patterns_16_8_2_verified, ⟨patterns_16_8_3_verified, ⟨patterns_16_8_4_verified, ⟨patterns_16_8_5_verified, ⟨patterns_16_8_6_verified, ⟨patterns_16_8_7_verified, ⟨patterns_16_8_8_verified, ⟨patterns_16_8_9_verified, ⟨patterns_16_8_10_verified, ⟨patterns_16_8_11_verified, ⟨patterns_16_8_12_verified, ⟨patterns_16_8_13_verified, ⟨patterns_16_8_14_verified, ⟨patterns_16_8_15_verified, ⟨patterns_16_8_16_verified, ⟨patterns_16_8_17_verified, ⟨patterns_16_8_18_verified, ⟨patterns_16_8_19_verified, ⟨patterns_16_8_20_verified, ⟨patterns_16_8_21_verified, ⟨patterns_16_8_22_verified, ⟨patterns_16_8_23_verified, ⟨patterns_16_8_24_verified, ⟨patterns_16_8_25_verified, ⟨patterns_16_8_26_verified, ⟨patterns_16_8_27_verified, ⟨patterns_16_8_28_verified, ⟨patterns_16_8_29_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_16_8_coverage : patternChoices 8 8 [] = patterns_16_8 := by decide +kernel

theorem finite_patterns_16_8_oai : ∀ D ∈ patternChoices 8 (16-8) [], PatternVerified 16 8 D := by

  rw [patterns_16_8_coverage]

  exact patterns_16_8_verified

end CycleClique

end OAI
end

theorem solution : type_of% @OAI.CycleClique.finite_patterns_16_8_oai := @OAI.CycleClique.finite_patterns_16_8_oai
