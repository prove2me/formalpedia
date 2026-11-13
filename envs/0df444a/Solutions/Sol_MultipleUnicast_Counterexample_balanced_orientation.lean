-- Prove2me | solution 1 for MultipleUnicast.Counterexample.balanced_orientation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T11:21:48.274329+00:00
-- url     : https://prove2.me/submissions/edd8c4b1-9f05-4431-96f0-f28f04207eff

import Mathlib
import Definitions.Def_MultipleUnicast_Counterexample_Graph
import Theorems.Thm_MultipleUnicast_Counterexample_incidenceList_indexing
import Theorems.Thm_MultipleUnicast_Counterexample_inDegree_univ_eq_five
import Theorems.Thm_MultipleUnicast_Counterexample_outDegree_univ_eq_five

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

/-! The incidence rows of PG(2,9), checked in ten small kernel computations. -/

namespace MultipleUnicast.Counterexample.Dev.IncRows
open MultipleUnicast.Counterexample

def rowT : List (List ℕ) := [[1, 10, 19, 28, 37, 46, 55, 64, 73, 82], [0, 10, 11, 12, 13, 14, 15, 16, 17, 18], [3, 10, 21, 29, 43, 54, 62, 67, 78, 86], [2, 10, 20, 30, 40, 50, 60, 70, 80, 90], [4, 10, 22, 34, 39, 51, 63, 65, 77, 89], [8, 10, 26, 33, 41, 48, 61, 72, 76, 83], [9, 10, 27, 32, 44, 49, 57, 69, 74, 88], [7, 10, 25, 31, 38, 53, 59, 66, 81, 87], [5, 10, 23, 36, 42, 52, 56, 71, 75, 85], [6, 10, 24, 35, 45, 47, 58, 68, 79, 84], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [1, 12, 21, 30, 39, 48, 57, 66, 75, 84], [1, 11, 20, 29, 38, 47, 56, 65, 74, 83], [1, 13, 22, 31, 40, 49, 58, 67, 76, 85], [1, 17, 26, 35, 44, 53, 62, 71, 80, 89], [1, 18, 27, 36, 45, 54, 63, 72, 81, 90], [1, 16, 25, 34, 43, 52, 61, 70, 79, 88], [1, 14, 23, 32, 41, 50, 59, 68, 77, 86], [1, 15, 24, 33, 42, 51, 60, 69, 78, 87], [0, 28, 29, 30, 31, 32, 33, 34, 35, 36], [3, 12, 20, 28, 45, 53, 61, 69, 77, 85], [2, 11, 21, 28, 41, 51, 58, 71, 81, 88], [4, 13, 25, 28, 42, 54, 57, 68, 80, 83], [8, 17, 24, 28, 39, 52, 59, 67, 74, 90], [9, 18, 23, 28, 40, 48, 62, 65, 79, 87], [7, 16, 22, 28, 44, 50, 56, 72, 78, 84], [5, 14, 27, 28, 43, 47, 60, 66, 76, 89], [6, 15, 26, 28, 38, 49, 63, 70, 75, 86], [0, 19, 20, 21, 22, 23, 24, 25, 26, 27], [2, 12, 19, 29, 42, 49, 59, 72, 79, 89], [3, 11, 19, 30, 44, 52, 63, 68, 76, 87], [7, 13, 19, 34, 41, 47, 62, 69, 75, 90], [6, 17, 19, 33, 40, 54, 56, 66, 77, 88], [5, 18, 19, 32, 38, 51, 61, 67, 80, 84], [4, 16, 19, 31, 45, 48, 60, 71, 74, 86], [9, 14, 19, 36, 39, 53, 58, 70, 78, 83], [8, 15, 19, 35, 43, 50, 57, 65, 81, 85], [0, 37, 38, 39, 40, 41, 42, 43, 44, 45], [7, 12, 27, 33, 37, 52, 58, 65, 80, 86], [4, 11, 23, 35, 37, 49, 61, 66, 78, 90], [3, 13, 24, 32, 37, 48, 56, 70, 81, 89], [5, 17, 21, 31, 37, 50, 63, 69, 79, 83], [8, 18, 22, 29, 37, 53, 60, 68, 75, 88], [2, 16, 26, 36, 37, 47, 57, 67, 77, 87], [6, 14, 25, 30, 37, 51, 62, 72, 74, 85], [9, 15, 20, 34, 37, 54, 59, 71, 76, 84], [0, 73, 74, 75, 76, 77, 78, 79, 80, 81], [9, 12, 26, 31, 43, 51, 56, 68, 73, 90], [5, 11, 24, 34, 40, 53, 57, 72, 73, 86], [6, 13, 27, 29, 39, 50, 61, 71, 73, 87], [3, 17, 25, 36, 41, 49, 60, 65, 73, 84], [4, 18, 21, 33, 44, 47, 59, 70, 73, 85], [8, 16, 23, 30, 38, 54, 58, 69, 73, 89], [7, 14, 20, 35, 42, 48, 63, 67, 73, 88], [2, 15, 22, 32, 45, 52, 62, 66, 73, 83], [0, 82, 83, 84, 85, 86, 87, 88, 89, 90], [8, 12, 25, 32, 40, 47, 63, 71, 78, 82], [6, 11, 22, 36, 43, 48, 59, 69, 80, 82], [9, 13, 21, 35, 38, 52, 60, 72, 77, 82], [7, 17, 23, 29, 45, 51, 57, 70, 76, 82], [3, 18, 26, 34, 42, 50, 58, 66, 74, 82], [5, 16, 20, 33, 39, 49, 62, 68, 81, 82], [2, 14, 24, 31, 44, 54, 61, 65, 75, 82], [4, 15, 27, 30, 41, 53, 56, 67, 79, 82], [0, 64, 65, 66, 67, 68, 69, 70, 71, 72], [4, 12, 24, 36, 38, 50, 62, 64, 76, 88], [7, 11, 26, 32, 39, 54, 60, 64, 79, 85], [2, 13, 23, 33, 43, 53, 63, 64, 74, 84], [9, 17, 22, 30, 42, 47, 61, 64, 81, 86], [6, 18, 20, 31, 41, 52, 57, 64, 78, 89], [3, 16, 27, 35, 40, 51, 59, 64, 75, 83], [8, 14, 21, 34, 45, 49, 56, 64, 80, 87], [5, 15, 25, 29, 44, 48, 58, 64, 77, 90], [0, 46, 47, 48, 49, 50, 51, 52, 53, 54], [6, 12, 23, 34, 44, 46, 60, 67, 81, 83], [8, 11, 27, 31, 42, 46, 62, 70, 77, 84], [5, 13, 26, 30, 45, 46, 59, 65, 78, 88], [4, 17, 20, 32, 43, 46, 58, 72, 75, 87], [2, 18, 25, 35, 39, 46, 56, 69, 76, 86], [9, 16, 24, 29, 41, 46, 63, 66, 80, 85], [3, 14, 22, 33, 38, 46, 57, 71, 79, 90], [7, 15, 21, 36, 40, 46, 61, 68, 74, 89], [0, 55, 56, 57, 58, 59, 60, 61, 62, 63], [5, 12, 22, 35, 41, 54, 55, 70, 74, 87], [9, 11, 25, 33, 45, 50, 55, 67, 75, 89], [8, 13, 20, 36, 44, 51, 55, 66, 79, 86], [2, 17, 27, 34, 38, 48, 55, 68, 78, 85], [7, 18, 24, 30, 43, 49, 55, 71, 77, 83], [6, 16, 21, 32, 42, 53, 55, 65, 76, 90], [4, 14, 26, 29, 40, 52, 55, 69, 81, 84], [3, 15, 23, 31, 39, 47, 55, 72, 80, 88]]

def row (i : Fin 91) : List ℕ :=
  ((List.finRange 91).filter fun j => dot (triple i) (triple j) = 0).map Fin.val

theorem row_chunk0 : ∀ i : Fin 91, 0 ≤ i.val → i.val < 10 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk1 : ∀ i : Fin 91, 10 ≤ i.val → i.val < 20 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk2 : ∀ i : Fin 91, 20 ≤ i.val → i.val < 30 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk3 : ∀ i : Fin 91, 30 ≤ i.val → i.val < 40 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk4 : ∀ i : Fin 91, 40 ≤ i.val → i.val < 50 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk5 : ∀ i : Fin 91, 50 ≤ i.val → i.val < 60 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk6 : ∀ i : Fin 91, 60 ≤ i.val → i.val < 70 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk7 : ∀ i : Fin 91, 70 ≤ i.val → i.val < 80 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk8 : ∀ i : Fin 91, 80 ≤ i.val → i.val < 90 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_chunk9 : ∀ i : Fin 91, 90 ≤ i.val → i.val < 100 → row i = rowT.getD i.val [] := by
  decide +kernel

theorem row_eq (i : Fin 91) : row i = rowT.getD i.val [] := by
  have h := i.isLt
  by_cases h0 : i.val < 10; · exact row_chunk0 i (by omega) h0
  by_cases h1 : i.val < 20; · exact row_chunk1 i (by omega) h1
  by_cases h2 : i.val < 30; · exact row_chunk2 i (by omega) h2
  by_cases h3 : i.val < 40; · exact row_chunk3 i (by omega) h3
  by_cases h4 : i.val < 50; · exact row_chunk4 i (by omega) h4
  by_cases h5 : i.val < 60; · exact row_chunk5 i (by omega) h5
  by_cases h6 : i.val < 70; · exact row_chunk6 i (by omega) h6
  by_cases h7 : i.val < 80; · exact row_chunk7 i (by omega) h7
  by_cases h8 : i.val < 90; · exact row_chunk8 i (by omega) h8
  exact row_chunk9 i (by omega) (by omega)

theorem incidenceList_map :
    incidenceList.map (fun p => (p.1.val, p.2.val)) =
      (List.finRange 91).flatMap (fun i => (rowT.getD i.val []).map (fun j => (i.val, j))) := by
  unfold incidenceList
  rw [List.map_flatMap]
  congr 1
  funext i
  rw [← row_eq, row, List.map_map, List.map_map]
  rfl

end MultipleUnicast.Counterexample.Dev.IncRows
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false
namespace MultipleUnicast.Counterexample.Dev.Bal
open MultipleUnicast.Counterexample

def headLs : List (List ℕ) := [[92,101,110,119,0,137,0,0,0,0,1,1,1,1,104,105,106,1,108,109,94,2,112,2,2,145,2,158,2,177,93,101,3,3,3,3,3,161,171,181,4,4,4,125,130,142,4,156,4,180,99,101,117,5,5,139,5,5,167,5,6,101,6,6,135,140,148,160,6,6,98,7,116,122,129,7,150,7,7,7,8,101,8,127,8,8,147,162,8,176,97],
  [9,115,9,9,9,149,9,170,175,91,10,93,10,95,10,10,98,10,100,11,11,112,121,11,11,11,157,166,175,92,12,12,120,129,138,147,12,12,12,13,104,13,13,131,13,149,158,13,176,14,14,14,14,135,144,153,162,14,180,92,15,15,127,15,15,154,15,172,181,92,107,116,16,16,143,16,16,16,179,92,105,17,17,17,141,17,159,168,17,18,18],
  [18,124,133,18,151,160,18,178,91,19,120,121,122,19,19,125,19,19,94,20,20,119,136,20,20,160,168,20,21,102,21,21,132,21,149,162,172,21,95,22,116,22,22,22,148,159,22,174,99,23,115,119,23,143,23,23,23,181,100,24,114,119,24,24,24,156,24,178,25,107,25,119,25,25,25,163,169,175,96,105,26,26,134,138,26,26,26,180,27,106,27],
  [27,27,140,27,161,166,177,91,110,28,112,28,28,115,28,117,28,93,29,29,29,133,29,29,163,170,180,30,30,110,121,135,30,154,159,30,30,98,104,110,125,31,31,153,31,31,31,97,32,110,32,32,32,147,32,168,179,96,33,33,123,33,142,152,33,171,33,34,107,34,34,136,34,151,162,165,34,100,35,35,35,130,144,35,161,169,35,36,106,36,36],
  [36,141,148,156,36,176,91,37,37,130,131,37,133,37,37,136,38,103,118,124,128,38,38,38,171,38,95,102,39,126,128,140,39,39,39,39,40,40,115,123,128,139,40,40,172,40,96,41,41,122,41,141,154,41,41,174,99,109,113,120,42,42,42,159,42,42,43,43,117,127,43,138,148,158,43,43,44,44,44,121,128,142,44,163,165,44,100,45,111,45,128],
  [45,45,45,167,175,46,46,165,166,167,168,46,46,171,46,47,103,47,47,134,142,147,47,164,47,96,102,48,48,48,144,48,163,48,177,49,104,118,49,49,49,152,49,164,178,94,108,116,127,132,50,50,50,50,50,51,109,112,124,51,51,150,51,164,51,52,107,114,52,52,145,52,160,164,52,53,53,111,53,133,53,53,158,164,179,54,54,113,123,54,54],
  [153,157,54,174,55,173,174,55,55,177,55,179,55,181,56,103,56,56,131,56,154,162,169,56,97,57,113,57,134,139,150,57,57,57,58,58,58,126,58,143,151,58,168,173,59,108,114,120,59,59,59,161,167,59,60,60,117,125,60,60,149,157,60,173,61,61,61,61,130,140,153,159,172,61,93,62,62,62,62,145,152,62,166,173,63,63,118,63,132,144,63],
  [63,170,173,64,64,156,157,64,64,160,161,64,163,95,103,65,65,129,141,65,155,65,65,98,66,66,66,66,145,151,155,170,66,93,67,114,124,134,67,67,67,165,67,68,108,113,68,133,138,68,68,172,68,69,69,111,69,132,143,69,155,69,180,94,107,118,126,70,70,70,70,70,174,71,71,71,71,136,71,147,155,171,178,72,106,72,72,135,139,149,155],
  [72,72,73,73,73,73,73,141,142,143,144,145,97,74,74,125,135,137,74,158,74,74,99,102,75,122,75,137,153,75,75,75,76,104,76,76,136,76,150,156,169,76,77,108,111,123,77,77,77,77,166,178,78,109,78,126,130,137,78,78,78,177,79,79,115,120,79,137,154,79,79,176,94,105,80,80,129,80,148,80,170,80,81,106,112,81,131,81,152,81,165],
  [81,91,146,82,82,82,150,151,152,82,82,96,103,113,126,132,83,83,83,83,83,100,102,116,124,84,84,146,84,84,84,99,85,111,127,85,85,146,157,85,85,86,86,118,86,129,139,86,86,169,176,98,109,87,121,134,140,87,87,87,87,97,88,88,123,88,88,146,88,167,181,95,105,117,89,131,89,89,89,89,175,90,90,114,122,90,138,146,90,90,179]]
def headL : List ℕ := headLs.flatten
def tailLs : List (List ℕ) := [[0,0,0,0,128,0,146,155,164,173,91,101,102,103,1,1,1,107,1,1,2,101,2,120,134,2,153,2,169,2,3,3,111,121,131,141,151,3,3,3,95,101,113,4,4,4,154,4,168,4,5,5,5,124,132,5,152,163,5,174,100,6,118,123,6,6,6,6,165,179,7,101,7,7,7,144,7,157,172,178,96,8,114,8,133,143,8,8,166,8,9],
  [101,9,126,136,138,9,159,9,9,10,92,10,94,10,96,97,10,99,10,92,103,11,11,130,139,148,11,11,11,12,102,111,12,12,12,12,156,165,174,92,13,113,122,13,140,13,13,167,13,92,108,117,126,14,14,14,14,171,14,15,109,118,15,136,145,15,163,15,15,16,16,16,125,134,16,152,161,170,16,17,17,114,123,132,17,150,17,17,177,92,106],
  [115,18,18,142,18,18,169,18,19,119,19,19,19,123,124,19,126,127,20,103,111,20,20,144,152,20,20,176,93,21,112,119,21,142,21,21,21,179,22,104,22,119,133,145,22,22,171,22,23,108,23,23,130,23,150,158,165,23,24,109,24,24,131,139,153,24,170,24,98,25,113,25,135,141,147,25,25,25,26,26,118,119,26,26,151,157,167,26,97,27,117],
  [119,129,27,154,27,27,27,28,28,111,28,113,114,28,116,28,118,29,103,110,120,29,140,150,29,29,29,94,102,30,30,30,143,30,30,167,178,31,31,31,31,132,138,31,160,166,181,32,108,32,124,131,145,32,157,32,32,33,109,110,33,129,33,33,158,33,175,95,34,110,122,34,139,34,34,34,177,35,105,110,127,35,35,149,35,35,174,99,36,110,126],
  [134,36,36,36,172,36,37,128,129,37,37,132,37,134,135,37,98,38,38,38,38,143,149,156,38,177,39,39,114,39,39,39,152,157,169,181,94,104,40,40,40,40,147,161,40,180,41,108,112,41,128,41,41,160,170,41,42,42,42,42,128,144,151,42,166,179,93,107,43,43,128,43,43,43,168,178,97,105,116,44,44,44,153,44,44,176,45,106,45,125,45],
  [145,150,162,45,45,91,164,46,46,46,46,169,170,46,172,100,47,117,122,47,47,47,159,47,181,48,48,115,125,131,48,148,48,164,48,97,49,49,120,130,141,49,162,49,49,50,50,50,50,50,140,151,156,164,175,95,51,51,51,135,138,51,161,51,176,99,52,52,121,129,52,149,52,52,180,98,105,53,126,53,139,154,53,53,53,93,106,54,54,136,143],
  [54,54,164,54,91,55,55,175,176,55,178,55,180,55,99,56,116,123,56,138,56,56,56,173,57,102,57,127,57,57,57,160,171,173,100,104,112,58,129,58,58,163,58,58,98,59,59,59,136,142,148,59,59,173,94,109,60,60,133,141,60,60,165,60,96,107,111,124,61,61,61,61,61,173,62,105,115,122,135,62,62,156,62,62,95,106,63,121,63,63,147],
  [158,63,63,91,155,64,64,158,159,64,64,162,64,65,65,115,127,65,65,153,65,167,179,66,102,117,123,130,66,66,66,66,176,67,104,67,67,67,144,154,155,67,175,100,68,68,121,68,68,152,155,68,177,97,109,69,122,69,69,148,69,169,69,70,70,70,70,131,142,150,155,166,70,99,105,112,125,71,140,71,71,71,71,96,72,116,120,72,72,72,72],
  [168,181,91,137,138,139,140,73,73,73,73,73,74,103,114,74,74,74,151,74,172,174,75,75,118,75,133,75,75,161,168,175,96,76,117,121,76,137,76,76,76,179,95,77,77,77,134,137,149,163,77,77,93,78,116,78,78,78,147,160,167,78,100,107,79,79,132,79,79,157,171,79,80,80,113,124,80,137,80,162,80,181,98,81,81,127,81,137,81,159,81],
  [180,82,82,147,148,149,82,82,82,153,154,83,83,83,83,83,145,146,161,165,178,84,84,84,84,136,141,84,158,166,180,85,104,85,85,135,142,85,85,170,177,93,108,86,125,86,86,146,159,86,86,87,87,115,87,87,87,146,162,168,174,88,107,112,88,133,144,88,156,88,88,89,89,89,120,89,143,146,160,172,89,94,106,90,90,130,90,90,163,171,90]]
def tailL : List ℕ := tailLs.flatten

def incTabs : List (List (ℕ × ℕ)) := [[(0,1),(0,10),(0,19),(0,28),(0,37),(0,46),(0,55),(0,64),(0,73),(0,82),(1,0),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18),(2,3),(2,10),(2,21),(2,29),(2,43),(2,54),(2,62),(2,67),(2,78),(2,86),(3,2),(3,10),(3,20),(3,30),(3,40),(3,50),(3,60),(3,70),(3,80),(3,90),(4,4),(4,10),(4,22),(4,34),(4,39),(4,51),(4,63),(4,65),(4,77),(4,89),(5,8),(5,10),(5,26),(5,33),(5,41),(5,48),(5,61),(5,72),(5,76),(5,83),(6,9),(6,10),(6,27),(6,32),(6,44),(6,49),(6,57),(6,69),(6,74),(6,88),(7,7),(7,10),(7,25),(7,31),(7,38),(7,53),(7,59),(7,66),(7,81),(7,87),(8,5),(8,10),(8,23),(8,36),(8,42),(8,52),(8,56),(8,71),(8,75),(8,85),(9,6)],
  [(9,10),(9,24),(9,35),(9,45),(9,47),(9,58),(9,68),(9,79),(9,84),(10,0),(10,1),(10,2),(10,3),(10,4),(10,5),(10,6),(10,7),(10,8),(10,9),(11,1),(11,12),(11,21),(11,30),(11,39),(11,48),(11,57),(11,66),(11,75),(11,84),(12,1),(12,11),(12,20),(12,29),(12,38),(12,47),(12,56),(12,65),(12,74),(12,83),(13,1),(13,13),(13,22),(13,31),(13,40),(13,49),(13,58),(13,67),(13,76),(13,85),(14,1),(14,17),(14,26),(14,35),(14,44),(14,53),(14,62),(14,71),(14,80),(14,89),(15,1),(15,18),(15,27),(15,36),(15,45),(15,54),(15,63),(15,72),(15,81),(15,90),(16,1),(16,16),(16,25),(16,34),(16,43),(16,52),(16,61),(16,70),(16,79),(16,88),(17,1),(17,14),(17,23),(17,32),(17,41),(17,50),(17,59),(17,68),(17,77),(17,86),(18,1),(18,15)],
  [(18,24),(18,33),(18,42),(18,51),(18,60),(18,69),(18,78),(18,87),(19,0),(19,28),(19,29),(19,30),(19,31),(19,32),(19,33),(19,34),(19,35),(19,36),(20,3),(20,12),(20,20),(20,28),(20,45),(20,53),(20,61),(20,69),(20,77),(20,85),(21,2),(21,11),(21,21),(21,28),(21,41),(21,51),(21,58),(21,71),(21,81),(21,88),(22,4),(22,13),(22,25),(22,28),(22,42),(22,54),(22,57),(22,68),(22,80),(22,83),(23,8),(23,17),(23,24),(23,28),(23,39),(23,52),(23,59),(23,67),(23,74),(23,90),(24,9),(24,18),(24,23),(24,28),(24,40),(24,48),(24,62),(24,65),(24,79),(24,87),(25,7),(25,16),(25,22),(25,28),(25,44),(25,50),(25,56),(25,72),(25,78),(25,84),(26,5),(26,14),(26,27),(26,28),(26,43),(26,47),(26,60),(26,66),(26,76),(26,89),(27,6),(27,15),(27,26)],
  [(27,28),(27,38),(27,49),(27,63),(27,70),(27,75),(27,86),(28,0),(28,19),(28,20),(28,21),(28,22),(28,23),(28,24),(28,25),(28,26),(28,27),(29,2),(29,12),(29,19),(29,29),(29,42),(29,49),(29,59),(29,72),(29,79),(29,89),(30,3),(30,11),(30,19),(30,30),(30,44),(30,52),(30,63),(30,68),(30,76),(30,87),(31,7),(31,13),(31,19),(31,34),(31,41),(31,47),(31,62),(31,69),(31,75),(31,90),(32,6),(32,17),(32,19),(32,33),(32,40),(32,54),(32,56),(32,66),(32,77),(32,88),(33,5),(33,18),(33,19),(33,32),(33,38),(33,51),(33,61),(33,67),(33,80),(33,84),(34,4),(34,16),(34,19),(34,31),(34,45),(34,48),(34,60),(34,71),(34,74),(34,86),(35,9),(35,14),(35,19),(35,36),(35,39),(35,53),(35,58),(35,70),(35,78),(35,83),(36,8),(36,15),(36,19),(36,35)],
  [(36,43),(36,50),(36,57),(36,65),(36,81),(36,85),(37,0),(37,37),(37,38),(37,39),(37,40),(37,41),(37,42),(37,43),(37,44),(37,45),(38,7),(38,12),(38,27),(38,33),(38,37),(38,52),(38,58),(38,65),(38,80),(38,86),(39,4),(39,11),(39,23),(39,35),(39,37),(39,49),(39,61),(39,66),(39,78),(39,90),(40,3),(40,13),(40,24),(40,32),(40,37),(40,48),(40,56),(40,70),(40,81),(40,89),(41,5),(41,17),(41,21),(41,31),(41,37),(41,50),(41,63),(41,69),(41,79),(41,83),(42,8),(42,18),(42,22),(42,29),(42,37),(42,53),(42,60),(42,68),(42,75),(42,88),(43,2),(43,16),(43,26),(43,36),(43,37),(43,47),(43,57),(43,67),(43,77),(43,87),(44,6),(44,14),(44,25),(44,30),(44,37),(44,51),(44,62),(44,72),(44,74),(44,85),(45,9),(45,15),(45,20),(45,34),(45,37)],
  [(45,54),(45,59),(45,71),(45,76),(45,84),(46,0),(46,73),(46,74),(46,75),(46,76),(46,77),(46,78),(46,79),(46,80),(46,81),(47,9),(47,12),(47,26),(47,31),(47,43),(47,51),(47,56),(47,68),(47,73),(47,90),(48,5),(48,11),(48,24),(48,34),(48,40),(48,53),(48,57),(48,72),(48,73),(48,86),(49,6),(49,13),(49,27),(49,29),(49,39),(49,50),(49,61),(49,71),(49,73),(49,87),(50,3),(50,17),(50,25),(50,36),(50,41),(50,49),(50,60),(50,65),(50,73),(50,84),(51,4),(51,18),(51,21),(51,33),(51,44),(51,47),(51,59),(51,70),(51,73),(51,85),(52,8),(52,16),(52,23),(52,30),(52,38),(52,54),(52,58),(52,69),(52,73),(52,89),(53,7),(53,14),(53,20),(53,35),(53,42),(53,48),(53,63),(53,67),(53,73),(53,88),(54,2),(54,15),(54,22),(54,32),(54,45),(54,52)],
  [(54,62),(54,66),(54,73),(54,83),(55,0),(55,82),(55,83),(55,84),(55,85),(55,86),(55,87),(55,88),(55,89),(55,90),(56,8),(56,12),(56,25),(56,32),(56,40),(56,47),(56,63),(56,71),(56,78),(56,82),(57,6),(57,11),(57,22),(57,36),(57,43),(57,48),(57,59),(57,69),(57,80),(57,82),(58,9),(58,13),(58,21),(58,35),(58,38),(58,52),(58,60),(58,72),(58,77),(58,82),(59,7),(59,17),(59,23),(59,29),(59,45),(59,51),(59,57),(59,70),(59,76),(59,82),(60,3),(60,18),(60,26),(60,34),(60,42),(60,50),(60,58),(60,66),(60,74),(60,82),(61,5),(61,16),(61,20),(61,33),(61,39),(61,49),(61,62),(61,68),(61,81),(61,82),(62,2),(62,14),(62,24),(62,31),(62,44),(62,54),(62,61),(62,65),(62,75),(62,82),(63,4),(63,15),(63,27),(63,30),(63,41),(63,53),(63,56)],
  [(63,67),(63,79),(63,82),(64,0),(64,64),(64,65),(64,66),(64,67),(64,68),(64,69),(64,70),(64,71),(64,72),(65,4),(65,12),(65,24),(65,36),(65,38),(65,50),(65,62),(65,64),(65,76),(65,88),(66,7),(66,11),(66,26),(66,32),(66,39),(66,54),(66,60),(66,64),(66,79),(66,85),(67,2),(67,13),(67,23),(67,33),(67,43),(67,53),(67,63),(67,64),(67,74),(67,84),(68,9),(68,17),(68,22),(68,30),(68,42),(68,47),(68,61),(68,64),(68,81),(68,86),(69,6),(69,18),(69,20),(69,31),(69,41),(69,52),(69,57),(69,64),(69,78),(69,89),(70,3),(70,16),(70,27),(70,35),(70,40),(70,51),(70,59),(70,64),(70,75),(70,83),(71,8),(71,14),(71,21),(71,34),(71,45),(71,49),(71,56),(71,64),(71,80),(71,87),(72,5),(72,15),(72,25),(72,29),(72,44),(72,48),(72,58),(72,64)],
  [(72,77),(72,90),(73,0),(73,46),(73,47),(73,48),(73,49),(73,50),(73,51),(73,52),(73,53),(73,54),(74,6),(74,12),(74,23),(74,34),(74,44),(74,46),(74,60),(74,67),(74,81),(74,83),(75,8),(75,11),(75,27),(75,31),(75,42),(75,46),(75,62),(75,70),(75,77),(75,84),(76,5),(76,13),(76,26),(76,30),(76,45),(76,46),(76,59),(76,65),(76,78),(76,88),(77,4),(77,17),(77,20),(77,32),(77,43),(77,46),(77,58),(77,72),(77,75),(77,87),(78,2),(78,18),(78,25),(78,35),(78,39),(78,46),(78,56),(78,69),(78,76),(78,86),(79,9),(79,16),(79,24),(79,29),(79,41),(79,46),(79,63),(79,66),(79,80),(79,85),(80,3),(80,14),(80,22),(80,33),(80,38),(80,46),(80,57),(80,71),(80,79),(80,90),(81,7),(81,15),(81,21),(81,36),(81,40),(81,46),(81,61),(81,68),(81,74)],
  [(81,89),(82,0),(82,55),(82,56),(82,57),(82,58),(82,59),(82,60),(82,61),(82,62),(82,63),(83,5),(83,12),(83,22),(83,35),(83,41),(83,54),(83,55),(83,70),(83,74),(83,87),(84,9),(84,11),(84,25),(84,33),(84,45),(84,50),(84,55),(84,67),(84,75),(84,89),(85,8),(85,13),(85,20),(85,36),(85,44),(85,51),(85,55),(85,66),(85,79),(85,86),(86,2),(86,17),(86,27),(86,34),(86,38),(86,48),(86,55),(86,68),(86,78),(86,85),(87,7),(87,18),(87,24),(87,30),(87,43),(87,49),(87,55),(87,71),(87,77),(87,83),(88,6),(88,16),(88,21),(88,32),(88,42),(88,53),(88,55),(88,65),(88,76),(88,90),(89,4),(89,14),(89,26),(89,29),(89,40),(89,52),(89,55),(89,69),(89,81),(89,84),(90,3),(90,15),(90,23),(90,31),(90,39),(90,47),(90,55),(90,72),(90,80),(90,88)]]
def incTab : List (ℕ × ℕ) := incTabs.flatten
def delNat : List ℕ := [7, 8, 9, 30, 31, 38, 39, 56, 57, 60, 68, 75, 79, 84, 88, 94, 102, 103, 117, 122, 127, 128, 141, 151, 154, 155, 157, 163, 164, 166, 167, 168, 176, 179, 183, 187, 203, 207, 208, 212, 215, 221, 224, 225, 231, 234, 236, 237, 238, 242, 243, 251, 253, 266, 282, 290, 300, 309, 318, 321, 324, 325, 330, 333, 338, 341, 349, 380, 386, 387, 389, 396, 398, 400, 401, 406, 407, 409, 411, 412, 418, 425, 426, 428, 439, 444, 454, 458, 464, 465, 468, 470, 476, 480, 481, 492, 502, 503, 504, 513, 517, 521, 522, 527, 539, 541, 544, 548, 552, 557, 559, 569, 579, 583, 585, 588, 592, 593, 598, 602, 603, 606, 607, 612, 619, 620, 632, 634, 643, 646, 670, 672, 673, 674, 682, 685, 688, 694, 695, 701, 702, 703, 709, 716, 718, 737, 746, 754, 757, 759, 773, 790, 821, 835, 837, 838, 839, 841, 842, 843, 846, 850, 853, 856, 857, 861, 862, 882, 884, 885, 887, 900, 901, 904, 907]
def posL : List ℕ := [23, 107, 125, 178, 86, 36, 27, 59, 40, 68, 81, 116, 49, 99, 69, 16, 2, 30, 154, 64, 165, 26, 32, 1, 141, 119, 38, 95, 62, 127, 50, 57, 15, 152, 90, 112, 98, 103, 7, 21, 9, 34, 33, 45, 113, 149, 146, 75, 145, 122, 172, 108, 132, 123, 5, 159, 71, 51, 169, 179, 176, 41, 144, 137, 142, 76, 115, 160, 171, 129, 161, 138, 72, 106, 78, 44, 120, 150, 61, 31, 92, 131, 102, 25, 167, 163, 88, 93, 6, 66, 14, 105, 53, 0, 175, 85, 39, 80, 117, 48, 168, 43, 46, 77, 126, 110, 133, 4, 181, 111, 82, 164, 134, 56, 18, 73, 60, 67, 13, 24, 65, 118, 70, 12, 11, 87, 63, 47, 22, 94, 114, 135, 28, 173, 96, 84, 166, 79, 54, 89, 97, 109, 153, 3, 157, 147, 17, 52, 100, 101, 124, 170, 158, 74, 83, 140, 143, 8, 128, 55, 29, 180, 91, 148, 136, 174, 156, 37, 42, 121, 139, 10, 58, 177, 35, 151, 104, 162, 155, 19, 130, 20]

theorem mem_deleted (q : Edge) : q ∈ deleted ↔ q.val ∈ delNat := by
  simp only [deleted, delNat, Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  rfl

theorem inc_eq : incidenceList.map (fun p => (p.1.val, p.2.val)) = incTab := by
  rw [MultipleUnicast.Counterexample.Dev.IncRows.incidenceList_map]; decide +kernel

theorem pos_eq : ∀ v : Vertex, position v = posL.getD v.val 0 := by decide +kernel

theorem getD_flatten91 {α : Type} (L : List (List α)) (d : α) (hL : ∀ l ∈ L, l.length = 91) :
    ∀ (k m : ℕ), m < 91 → L.flatten.getD (91 * k + m) d = (L.getD k []).getD m d := by
  induction L with
  | nil => intro k m _; simp
  | cons l L ih =>
    intro k m hm
    have hl : l.length = 91 := hL l (by simp)
    rw [List.flatten_cons]
    cases k with
    | zero =>
      rw [List.getD_append _ _ _ _ (by omega)]; simp
    | succ k =>
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have : 91 * (k + 1) + m - l.length = 91 * k + m := by omega
      rw [this, ih (fun l' hl' => hL l' (by simp [hl'])) k m hm]
      simp

theorem incTabs_len : ∀ l ∈ incTabs, l.length = 91 := by decide +kernel
theorem headLs_len : ∀ l ∈ headLs, l.length = 91 := by decide +kernel
theorem tailLs_len : ∀ l ∈ tailLs, l.length = 91 := by decide +kernel

theorem split91 (n : ℕ) : n = 91 * (n / 91) + n % 91 := (Nat.div_add_mod n 91).symm

theorem edgePair_vals (q : Edge) :
    ((edgePair q).1.val, (edgePair q).2.val) = incTab.getD q.val (0,0) := by
  have h0 : ((0, 0) : ℕ × ℕ) = (fun p : Fin 91 × Fin 91 => (p.1.val, p.2.val)) (0, 0) := rfl
  rw [← inc_eq, h0, List.getD_map]
  rfl

theorem edgePair_fst (q : Edge) : ((edgePair q).1.val) = (incTab.getD q.val (0,0)).1 := by
  rw [← edgePair_vals]

theorem edgePair_snd (q : Edge) : ((edgePair q).2.val) = (incTab.getD q.val (0,0)).2 := by
  rw [← edgePair_vals]

def pe (n : ℕ) : ℕ := (incTab.getD n (0,0)).1
def le (n : ℕ) : ℕ := 91 + (incTab.getD n (0,0)).2
def hn (n p l : ℕ) : ℕ :=
  if n ∈ delNat then (if posL.getD p 0 < posL.getD l 0 then p else l)
  else (if posL.getD p 0 < posL.getD l 0 then l else p)
def tn (n p l : ℕ) : ℕ :=
  if n ∈ delNat then (if posL.getD p 0 < posL.getD l 0 then l else p)
  else (if posL.getD p 0 < posL.getD l 0 then p else l)
def headNat (n : ℕ) : ℕ := hn n (pe n) (le n)
def tailNat (n : ℕ) : ℕ := tn n (pe n) (le n)

theorem pointEnd_val (q : Edge) : (pointEnd q).val = pe q.val := by
  simp only [pointEnd, pe, edgePair_fst]

theorem lineEnd_val (q : Edge) : (lineEnd q).val = le q.val := by
  simp only [lineEnd, le, edgePair_snd]

theorem head_val (q : Edge) : (head q).val = headNat q.val := by
  unfold head earlier later headNat hn
  simp only [mem_deleted, pos_eq, pointEnd_val, lineEnd_val]
  split_ifs <;> simp [pointEnd_val, lineEnd_val]

theorem tail_val (q : Edge) : (tail q).val = tailNat q.val := by
  unfold tail earlier later tailNat tn
  simp only [mem_deleted, pos_eq, pointEnd_val, lineEnd_val]
  split_ifs <;> simp [pointEnd_val, lineEnd_val]


theorem head_chunk0 : ∀ m, m < 91 → hn (91 * 0 + m) ((incTabs.getD 0 []).getD m (0,0)).1
    (91 + ((incTabs.getD 0 []).getD m (0,0)).2) = (headLs.getD 0 []).getD m 0 := by
  decide +kernel
theorem head_chunk1 : ∀ m, m < 91 → hn (91 * 1 + m) ((incTabs.getD 1 []).getD m (0,0)).1
    (91 + ((incTabs.getD 1 []).getD m (0,0)).2) = (headLs.getD 1 []).getD m 0 := by
  decide +kernel
theorem head_chunk2 : ∀ m, m < 91 → hn (91 * 2 + m) ((incTabs.getD 2 []).getD m (0,0)).1
    (91 + ((incTabs.getD 2 []).getD m (0,0)).2) = (headLs.getD 2 []).getD m 0 := by
  decide +kernel
theorem head_chunk3 : ∀ m, m < 91 → hn (91 * 3 + m) ((incTabs.getD 3 []).getD m (0,0)).1
    (91 + ((incTabs.getD 3 []).getD m (0,0)).2) = (headLs.getD 3 []).getD m 0 := by
  decide +kernel
theorem head_chunk4 : ∀ m, m < 91 → hn (91 * 4 + m) ((incTabs.getD 4 []).getD m (0,0)).1
    (91 + ((incTabs.getD 4 []).getD m (0,0)).2) = (headLs.getD 4 []).getD m 0 := by
  decide +kernel
theorem head_chunk5 : ∀ m, m < 91 → hn (91 * 5 + m) ((incTabs.getD 5 []).getD m (0,0)).1
    (91 + ((incTabs.getD 5 []).getD m (0,0)).2) = (headLs.getD 5 []).getD m 0 := by
  decide +kernel
theorem head_chunk6 : ∀ m, m < 91 → hn (91 * 6 + m) ((incTabs.getD 6 []).getD m (0,0)).1
    (91 + ((incTabs.getD 6 []).getD m (0,0)).2) = (headLs.getD 6 []).getD m 0 := by
  decide +kernel
theorem head_chunk7 : ∀ m, m < 91 → hn (91 * 7 + m) ((incTabs.getD 7 []).getD m (0,0)).1
    (91 + ((incTabs.getD 7 []).getD m (0,0)).2) = (headLs.getD 7 []).getD m 0 := by
  decide +kernel
theorem head_chunk8 : ∀ m, m < 91 → hn (91 * 8 + m) ((incTabs.getD 8 []).getD m (0,0)).1
    (91 + ((incTabs.getD 8 []).getD m (0,0)).2) = (headLs.getD 8 []).getD m 0 := by
  decide +kernel
theorem head_chunk9 : ∀ m, m < 91 → hn (91 * 9 + m) ((incTabs.getD 9 []).getD m (0,0)).1
    (91 + ((incTabs.getD 9 []).getD m (0,0)).2) = (headLs.getD 9 []).getD m 0 := by
  decide +kernel
theorem headNat_eq (n : ℕ) (h : n < 910) : headNat n = headL.getD n 0 := by
  have hm : n % 91 < 91 := Nat.mod_lt _ (by norm_num)
  have hk : n / 91 < 10 := by omega
  unfold headNat pe le
  rw [split91 n, incTab, headL, getD_flatten91 _ _ incTabs_len _ _ hm, getD_flatten91 _ _ headLs_len _ _ hm]
  generalize n / 91 = k at hk
  generalize n % 91 = m at hm
  interval_cases k
  · exact head_chunk0 m hm
  · exact head_chunk1 m hm
  · exact head_chunk2 m hm
  · exact head_chunk3 m hm
  · exact head_chunk4 m hm
  · exact head_chunk5 m hm
  · exact head_chunk6 m hm
  · exact head_chunk7 m hm
  · exact head_chunk8 m hm
  · exact head_chunk9 m hm

theorem tail_chunk0 : ∀ m, m < 91 → tn (91 * 0 + m) ((incTabs.getD 0 []).getD m (0,0)).1
    (91 + ((incTabs.getD 0 []).getD m (0,0)).2) = (tailLs.getD 0 []).getD m 0 := by
  decide +kernel
theorem tail_chunk1 : ∀ m, m < 91 → tn (91 * 1 + m) ((incTabs.getD 1 []).getD m (0,0)).1
    (91 + ((incTabs.getD 1 []).getD m (0,0)).2) = (tailLs.getD 1 []).getD m 0 := by
  decide +kernel
theorem tail_chunk2 : ∀ m, m < 91 → tn (91 * 2 + m) ((incTabs.getD 2 []).getD m (0,0)).1
    (91 + ((incTabs.getD 2 []).getD m (0,0)).2) = (tailLs.getD 2 []).getD m 0 := by
  decide +kernel
theorem tail_chunk3 : ∀ m, m < 91 → tn (91 * 3 + m) ((incTabs.getD 3 []).getD m (0,0)).1
    (91 + ((incTabs.getD 3 []).getD m (0,0)).2) = (tailLs.getD 3 []).getD m 0 := by
  decide +kernel
theorem tail_chunk4 : ∀ m, m < 91 → tn (91 * 4 + m) ((incTabs.getD 4 []).getD m (0,0)).1
    (91 + ((incTabs.getD 4 []).getD m (0,0)).2) = (tailLs.getD 4 []).getD m 0 := by
  decide +kernel
theorem tail_chunk5 : ∀ m, m < 91 → tn (91 * 5 + m) ((incTabs.getD 5 []).getD m (0,0)).1
    (91 + ((incTabs.getD 5 []).getD m (0,0)).2) = (tailLs.getD 5 []).getD m 0 := by
  decide +kernel
theorem tail_chunk6 : ∀ m, m < 91 → tn (91 * 6 + m) ((incTabs.getD 6 []).getD m (0,0)).1
    (91 + ((incTabs.getD 6 []).getD m (0,0)).2) = (tailLs.getD 6 []).getD m 0 := by
  decide +kernel
theorem tail_chunk7 : ∀ m, m < 91 → tn (91 * 7 + m) ((incTabs.getD 7 []).getD m (0,0)).1
    (91 + ((incTabs.getD 7 []).getD m (0,0)).2) = (tailLs.getD 7 []).getD m 0 := by
  decide +kernel
theorem tail_chunk8 : ∀ m, m < 91 → tn (91 * 8 + m) ((incTabs.getD 8 []).getD m (0,0)).1
    (91 + ((incTabs.getD 8 []).getD m (0,0)).2) = (tailLs.getD 8 []).getD m 0 := by
  decide +kernel
theorem tail_chunk9 : ∀ m, m < 91 → tn (91 * 9 + m) ((incTabs.getD 9 []).getD m (0,0)).1
    (91 + ((incTabs.getD 9 []).getD m (0,0)).2) = (tailLs.getD 9 []).getD m 0 := by
  decide +kernel
theorem tailNat_eq (n : ℕ) (h : n < 910) : tailNat n = tailL.getD n 0 := by
  have hm : n % 91 < 91 := Nat.mod_lt _ (by norm_num)
  have hk : n / 91 < 10 := by omega
  unfold tailNat pe le
  rw [split91 n, incTab, tailL, getD_flatten91 _ _ incTabs_len _ _ hm, getD_flatten91 _ _ tailLs_len _ _ hm]
  generalize n / 91 = k at hk
  generalize n % 91 = m at hm
  interval_cases k
  · exact tail_chunk0 m hm
  · exact tail_chunk1 m hm
  · exact tail_chunk2 m hm
  · exact tail_chunk3 m hm
  · exact tail_chunk4 m hm
  · exact tail_chunk5 m hm
  · exact tail_chunk6 m hm
  · exact tail_chunk7 m hm
  · exact tail_chunk8 m hm
  · exact tail_chunk9 m hm

theorem head_eq (q : Edge) : (head q).val = headL.getD q.val 0 := by
  rw [head_val, headNat_eq _ q.isLt]
theorem tail_eq (q : Edge) : (tail q).val = tailL.getD q.val 0 := by
  rw [tail_val, tailNat_eq _ q.isLt]


end MultipleUnicast.Counterexample.Dev.Bal
end

section
set_option maxRecDepth 4096
set_option autoImplicit false
set_option Elab.async false

namespace MultipleUnicast.Counterexample.Dev.BalMain
open MultipleUnicast.Counterexample MultipleUnicast.Counterexample.Dev.Bal

def headAt (n : ℕ) : ℕ := (headLs.getD (n / 91) []).getD (n % 91) 0
def tailAt (n : ℕ) : ℕ := (tailLs.getD (n / 91) []).getD (n % 91) 0

theorem head_at (q : Edge) : (head q).val = headAt q.val := by
  rw [head_eq, headL, split91 q.val, getD_flatten91 _ _ headLs_len _ _ (Nat.mod_lt _ (by norm_num)),
    headAt, ← split91]

theorem tail_at (q : Edge) : (tail q).val = tailAt q.val := by
  rw [tail_eq, tailL, split91 q.val, getD_flatten91 _ _ tailLs_len _ _ (Nat.mod_lt _ (by norm_num)),
    tailAt, ← split91]

def CL : List ℕ := [102,163,164,341,386,406,476,513,862]
def JL : List ℕ := [103,349,470,517,603,606,674,716,861]

theorem C_eq : C = (CL.map (fun n => (⟨n % 910, Nat.mod_lt _ (by norm_num)⟩ : Edge))).toFinset := by
  decide +kernel
theorem J_eq : J = (JL.map (fun n => (⟨n % 910, Nat.mod_lt _ (by norm_num)⟩ : Edge))).toFinset := by
  decide +kernel

theorem CJ_tab : ∀ v : Fin 182, (CL.filter (fun n => tailAt n = v.val)).length =
    (JL.filter (fun n => headAt n = v.val)).length := by decide +kernel

theorem card_filter_map (L : List ℕ) (hL : L.Nodup) (hlt : ∀ n ∈ L, n < 910) (f : Edge → ℕ) (g : ℕ → ℕ)
    (hfg : ∀ q : Edge, f q = g q.val) (v : ℕ) :
    (((L.map (fun n => (⟨n % 910, Nat.mod_lt _ (by norm_num)⟩ : Edge))).toFinset).filter
      (fun q => f q = v)).card = (L.filter (fun n => g n = v)).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha : a < 910 := hlt a (by simp)
    have hnot : a ∉ L := (List.nodup_cons.1 hL).1
    rw [List.map_cons, List.toFinset_cons, Finset.filter_insert, List.filter_cons]
    have hmem : (⟨a % 910, Nat.mod_lt _ (by norm_num)⟩ : Edge) ∉
        (L.map (fun n => (⟨n % 910, Nat.mod_lt _ (by norm_num)⟩ : Edge))).toFinset := by
      simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
      intro b hb heq
      have hb' := hlt b (by simp [hb])
      have := congrArg Fin.val heq
      simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb'] at this
      exact hnot (this ▸ hb)
    have ih' := ih (List.nodup_cons.1 hL).2 (fun n hn => hlt n (by simp [hn]))
    have e : g (a % 910) = g a := congrArg g (Nat.mod_eq_of_lt ha)
    rw [hfg]
    simp only [e]
    by_cases h : g a = v
    · simp only [h, if_true, decide_true]
      rw [Finset.card_insert_of_notMem (fun hh => hmem (Finset.mem_of_mem_filter _ hh)), ih']
      rfl
    · simp only [h, if_false, decide_false]
      exact ih'

theorem CJ_ok (v : Vertex) : outDegree C v = inDegree J v := by
  unfold outDegree inDegree
  have h1 : ((C.filter (fun q => tail q = v))).card = (CL.filter (fun n => tailAt n = v.val)).length := by
    rw [C_eq, ← card_filter_map CL (by decide) (by decide) (fun q => (tail q).val) tailAt tail_at v.val]
    congr 1; ext q; simp [Fin.ext_iff]
  have h2 : ((J.filter (fun q => head q = v))).card = (JL.filter (fun n => headAt n = v.val)).length := by
    rw [J_eq, ← card_filter_map JL (by decide) (by decide) (fun q => (head q).val) headAt head_at v.val]
    congr 1; ext q; simp [Fin.ext_iff]
  rw [h1, h2, CJ_tab v]

theorem small_cards : deleted.card = 175 ∧ C.card = 9 ∧ J.card = 9 ∧ C ⊆ deleted ∧ J ⊆ deleted ∧
    Disjoint C J := by decide +kernel

theorem cards : deleted.card = 175 ∧ C.card = 9 ∧ J.card = 9 ∧ C ⊆ deleted ∧ J ⊆ deleted ∧
    Disjoint C J ∧ B.card = 157 ∧ physical.card = 735 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := small_cards
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · rw [B, Finset.card_sdiff_of_subset (Finset.union_subset h4 h5), Finset.card_union_of_disjoint h6, h1, h2, h3]
  · rw [physical, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, h1]

theorem order_nodup : processingOrder.Nodup := by decide +kernel
theorem order_len : processingOrder.length = 182 := by decide +kernel

theorem perm_ok : processingOrder.Perm (List.finRange 182) := by
  apply List.perm_of_nodup_nodup_toFinset_eq order_nodup (List.nodup_finRange 182)
  rw [List.toFinset_finRange]
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup order_nodup, order_len, Fintype.card_fin]

end MultipleUnicast.Counterexample.Dev.BalMain

namespace MultipleUnicast.Counterexample
open MultipleUnicast.Counterexample.Dev.BalMain in
theorem chk_balanced_orientation :
    incidenceList.length = 910 ∧ incidenceList.Nodup ∧ Function.Injective edgePair ∧
    processingOrder.Perm (List.finRange 182) ∧
    deleted.card = 175 ∧ C.card = 9 ∧ J.card = 9 ∧
    C ⊆ deleted ∧ J ⊆ deleted ∧ Disjoint C J ∧
    B.card = 157 ∧ physical.card = 735 ∧
    ∀ v : Vertex,
      inDegree Finset.univ v = 5 ∧ outDegree Finset.univ v = 5 ∧
      outDegree C v = inDegree J v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := cards
  obtain ⟨i1, i2, i3⟩ := incidenceList_indexing
  exact ⟨i1, i2, i3, perm_ok, h1, h2, h3, h4, h5, h6, h7, h8,
    fun v => ⟨inDegree_univ_eq_five v, outDegree_univ_eq_five v, CJ_ok v⟩⟩
end MultipleUnicast.Counterexample
end

theorem solution : type_of% @MultipleUnicast.Counterexample.chk_balanced_orientation := @MultipleUnicast.Counterexample.chk_balanced_orientation
